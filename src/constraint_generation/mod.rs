use cwe_checker_lib::{
    analysis::graph::{Edge, Graph, Node},
    intermediate_representation::{
        Arg, BinOpType, Bitvector, Blk, Def, ExternSymbol, Jmp, Sub, Term, UnOpType,
    },
};

use log::{info, warn};
use petgraph::{graph::NodeIndex, visit::EdgeRef, EdgeDirection};

use cwe_checker_lib::intermediate_representation::{ByteSize, Expression, Variable};

use cwe_checker_lib::intermediate_representation::Tid;

use crate::constraints::{
    AddConstraint, ConstraintSet, DerivedTypeVar, Field, FieldLabel, SubtypeConstraint,
    TyConstraint, TypeVariable, VariableManager,
};

use std::{
    collections::{btree_set::BTreeSet, BTreeMap, HashMap, HashSet},
    convert::TryInto,
};

/// Gets a type variable for a [Tid] where multiple type variables need to exist at that [Tid] which are distinguished by which [Variable] they operate over.
pub fn tid_indexed_by_variable(tid: &Tid, var: &Variable) -> TypeVariable {
    TypeVariable::new(tid.get_str_repr().to_owned() + "_" + &var.name)
}

/// Converts a [Tid] to a [TypeVariable] by retrieving the string representation of the TID
pub fn tid_to_tvar(tid: &Tid) -> TypeVariable {
    // TODO(Ian): maybe change tids to store types?
    if tid.get_str_repr().starts_with("glb_") {
        TypeVariable::new_global(tid.get_str_repr().to_owned())
    } else {
        TypeVariable::new(tid.get_str_repr().to_owned())
    }
}

/// Converts a [Tid] to a [TypeVariable] by retrieving the string representation of the TID
pub fn tid_to_tvar_with_tag(tid: &Tid, tag: &Tid) -> TypeVariable {
    TypeVariable::with_tag(tid.get_str_repr().to_owned(), tag.clone())
}

/// Converts a term to a TypeVariable by using its unique term identifier (Tid).
pub fn term_to_tvar<T>(term: &Term<T>) -> TypeVariable {
    tid_to_tvar(&term.tid)
}

/// Converts a term to a TypeVariable by using its unique term identifier (Tid). Takes by the TID of the other term.
pub fn term_to_tvar_with_tag<T, V>(term: &Term<T>, tag: &Term<V>) -> TypeVariable {
    tid_to_tvar_with_tag(&term.tid, &tag.tid)
}

/// Creates an actual argument type variable for the procedure
pub fn arg_tvar(index: usize, target_sub: &Tid) -> TypeVariable {
    TypeVariable::new(format!("arg_{}_{}", target_sub.get_str_repr(), index))
}

/// A [NodeContextMapping] provides information about the program state at a given CFG node. Because basic blocks contain multiple defs
/// contexts must be capable of reapplying def terms to compute the intermediate states.
pub trait NodeContextMapping: Clone {
    /// Applys the given definition term to the state to compute the state after this def's affects have been applied to the state.
    fn apply_def(&self, term: &Term<Def>) -> Self;

    /// Applys a return to this node computing the post condition implied by the analyses after the return targetting a given block.
    fn apply_return_node(&self, call_term: &Term<Jmp>, return_term: &Term<Jmp>) -> Self;
}

/// Maps a variable (register) to it's representing type variable at this time step in the program. This type variable is some representation of
/// all reaching definitions of this register.
pub trait RegisterMapping: NodeContextMapping {
    /// Returns the set of TypeVariables that define the target variable at this point. We return the set rather than grouped constraints so that the client can decide the direction in which constraints should go
    fn access(&self, var: &Variable) -> BTreeSet<TypeVariable>;
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
/// Describes a [TypeVariable] for an abstract memory location where the acess may occur at some fixed offset into the type variable's cell.
pub struct TypeVariableAccess {
    /// The type variable which is accessed
    pub ty_var: TypeVariable,
    /// The size of the access
    pub sz: ByteSize,
    /// The potential constant offset at which the access occurs
    pub offset: Option<i64>,
}

/// Maps an address expression and a size to the possible type variables representing the loaded address at this program point.
/// Implementors of this trait effectively act as memory managers for the type inference algorithm.
pub trait PointsToMapping: NodeContextMapping {
    /// Gets the set of type variables this address expression points to.
    fn points_to(&self, address: &Expression, sz: ByteSize) -> BTreeSet<TypeVariableAccess>;

    /// Attempts to resolve a pointer expression to a variable
    fn get_pointer_variable(
        &self,
        address: &Expression,
        constant_resolver: &impl ConstantResolver,
    ) -> Option<DerivedTypeVar>;
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
/// An arg can either be a memory access (generally passed via the stack), or directly avialable in a variable.
pub enum ArgTvar {
    /// Describes how to access the argument as a memory variable.
    MemTvar(TypeVariableAccess),
    /// Describes an argument in a register.
    VariableTvar(TypeVariable),
}

/// Links formal parameters with the type variable for their actual argument at callsites.
/// Additionally, links actual returns to formal returns at return sites.
pub trait SubprocedureLocators: NodeContextMapping {
    // TODO(ian) may need the subprocedure tid here.
    /// Takes a points-to and register mapping to resolve type variables of inputs and outputs
    fn get_type_variables_and_constraints_for_arg(
        &self,
        arg: &Arg,
        reg: &impl RegisterMapping,
        points_to: &impl PointsToMapping,
        vm: &mut VariableManager,
    ) -> BTreeSet<ArgTvar>;
}

/// Represents analysis results that can convert accesses to constant addresses to global variables.
/// An analysis that partitions global variables should implement this trait.
pub trait ConstantResolver: NodeContextMapping {
    /// Produces a type variable for an access to the given address. A [VariableManager] is passed to allow
    /// the resolver to generate guarenteed fresh ephemeral variables.
    fn resolve_constant_to_variable(
        &self,
        target: &cwe_checker_lib::intermediate_representation::Bitvector,
        vman: &mut crate::constraints::VariableManager,
    ) -> crate::constraints::DerivedTypeVar {
        self.maybe_resolve_constant_to_variable(target)
            .unwrap_or_else(|| DerivedTypeVar::new(vman.fresh()))
    }

    /// Produces a variable only if there is an exact match, does not force resolution
    fn maybe_resolve_constant_to_variable(&self, target: &Bitvector) -> Option<DerivedTypeVar>;
}

// TODO(ian): this should have some sort of function on it that takes a lambda and basically joins constraints together to acess the derived type variable or something to prevent
// issues where constraints are forgetten, this is perhaps a functor tbh
struct BaseValueDomain {
    pub repr_var: DerivedTypeVar,
    pub additional_constriants: ConstraintSet,
}

impl BaseValueDomain {
    fn merge(
        self,
        BaseValueDomain {
            repr_var,
            mut additional_constriants,
        }: BaseValueDomain,
        f: &impl Fn(DerivedTypeVar, DerivedTypeVar, ConstraintSet) -> BaseValueDomain,
    ) -> BaseValueDomain {
        additional_constriants.insert_all(&self.additional_constriants);
        f(self.repr_var, repr_var, additional_constriants)
    }
}

impl From<(DerivedTypeVar, ConstraintSet)> for BaseValueDomain {
    fn from(t: (DerivedTypeVar, ConstraintSet)) -> Self {
        BaseValueDomain {
            repr_var: t.0,
            additional_constriants: t.1,
        }
    }
}

impl From<BaseValueDomain> for (DerivedTypeVar, ConstraintSet) {
    fn from(bv: BaseValueDomain) -> Self {
        (bv.repr_var, bv.additional_constriants)
    }
}

// this is kinda a hack
// Maybe there is a cleaner way to introduce the rule
// Var x.+y.load.field{size=a, offset=b}
// --------------------------------------
//  Var x.load.field{size=a, offset=b+y}
//As well as  Var +x.+y -> Var +(x+y)
/// Distributes adds into a field if possible
pub fn simplify_path(orig: &DerivedTypeVar) -> DerivedTypeVar {
    let pth = orig.get_field_labels();
    let mut new_path = Vec::new();
    let mut delayed_adds = Vec::new();
    let mut ind = 0;

    fn handle_adds_and_orig(
        new_path: &mut Vec<FieldLabel>,
        adds: &mut Vec<&i128>,
        orig: FieldLabel,
    ) {
        adds.drain(..)
            .for_each(|x| new_path.push(FieldLabel::Add(*x)));
        new_path.push(orig);
    }

    while ind < pth.len() {
        match &pth[ind] {
            FieldLabel::Add(cst) => delayed_adds.push(cst),
            FieldLabel::Load | FieldLabel::Store => {
                let loadorstore = pth[ind].clone();
                if ind < pth.len() - 1 {
                    let next = ind + 1;
                    if let FieldLabel::Field(fld) = &pth[next] {
                        let mut new_fld = fld.clone();
                        let total: i128 = delayed_adds.drain(..).copied().sum();
                        let total: i64 =
                            total.try_into().expect("Sums of adds should fit in an i64");
                        new_fld.offset += total;
                        new_path.push(loadorstore);
                        new_path.push(FieldLabel::Field(new_fld));
                        ind += 1;
                    } else {
                        handle_adds_and_orig(&mut new_path, &mut delayed_adds, loadorstore);
                    }
                } else {
                    handle_adds_and_orig(&mut new_path, &mut delayed_adds, loadorstore);
                }
            }
            _ => handle_adds_and_orig(&mut new_path, &mut delayed_adds, pth[ind].clone()),
        }
        ind += 1;
    }
    delayed_adds
        .drain(..)
        .for_each(|x| new_path.push(FieldLabel::Add(*x)));

    DerivedTypeVar::create_with_path(orig.get_base_variable().clone(), new_path)
}

/// Represents the flow-sensitive context needed by flow-insensitive constraint generation to generate type variables and constraints at a given program point.
/// The register mapping provides constraints and type variables to represent a register when it is accessed via some notion of reaching definitions.
/// The PointsToMapping determines the set of a type variables a load or store points to in order to generate constraints.
/// Finally the SubprocedureLocators are used to link actual and formal arguments and returns within constraints.
#[derive(Clone)]
pub struct NodeContext<
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    C: ConstantResolver,
> {
    reg_map: R,
    points_to: P,
    subprocedure_locators: S,
    constant_resolver: C,
    weakest_integral_type: TypeVariable,
}

/// Stores information about a given invocation of a subprocedure, either formal or actual (represented by a present callsite)
struct SubprocedureInvocation<'a, T> {
    calling_blk: Option<&'a Term<Blk>>,
    sub: &'a Term<T>,
    args: &'a [Arg],
}

impl<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators, C: ConstantResolver>
    NodeContextMapping for NodeContext<R, P, S, C>
{
    fn apply_def(&self, term: &Term<Def>) -> Self {
        let r = self.reg_map.apply_def(term);
        let p = self.points_to.apply_def(term);
        let s = self.subprocedure_locators.apply_def(term);
        let c = self.constant_resolver.apply_def(term);
        NodeContext::new(r, p, s, c, self.weakest_integral_type.clone())
    }

    fn apply_return_node(&self, call_term: &Term<Jmp>, return_term: &Term<Jmp>) -> Self {
        let r = self.reg_map.apply_return_node(call_term, return_term);
        let p = self.points_to.apply_return_node(call_term, return_term);
        let s = self
            .subprocedure_locators
            .apply_return_node(call_term, return_term);
        let c = self
            .constant_resolver
            .apply_return_node(call_term, return_term);
        NodeContext::new(r, p, s, c, self.weakest_integral_type.clone())
    }
}

impl<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators, C: ConstantResolver>
    NodeContext<R, P, S, C>
{
    /// Given a register, pointer, and subprocedure mapping, generates a full NodeContext.
    pub fn new(
        r: R,
        p: P,
        s: S,
        c: C,
        weakest_integral_type: TypeVariable,
    ) -> NodeContext<R, P, S, C> {
        NodeContext {
            reg_map: r,
            points_to: p,
            subprocedure_locators: s,
            constant_resolver: c,
            weakest_integral_type,
        }
    }

    fn generate_const_add_repr(bv: Bitvector, mut expr_repr: BaseValueDomain) -> BaseValueDomain {
        let constant = bv
            .try_to_i128()
            .expect("unable to get constant addition as i128");

        expr_repr
            .repr_var
            .add_field_label(FieldLabel::Add(constant));
        expr_repr
    }

    fn eval_add(
        &self,
        lhs: &Expression,
        rhs: &Expression,
        defining_tvars_are_subtype_of_repr: bool,
        vman: &mut VariableManager,
    ) -> (DerivedTypeVar, ConstraintSet) {
        match (lhs, rhs) {
            (Expression::Const(lhs_const), other_e) => Self::generate_const_add_repr(
                lhs_const.to_owned(),
                BaseValueDomain::from(self.evaluate_expression(
                    other_e,
                    defining_tvars_are_subtype_of_repr,
                    vman,
                )),
            )
            .into(),
            (other_e, Expression::Const(rhs_const)) => Self::generate_const_add_repr(
                rhs_const.to_owned(),
                BaseValueDomain::from(self.evaluate_expression(
                    other_e,
                    defining_tvars_are_subtype_of_repr,
                    vman,
                )),
            )
            .into(),
            (exp_lhs, exp_rhs) => {
                let exp1_repr = BaseValueDomain::from(self.evaluate_expression(
                    exp_lhs,
                    defining_tvars_are_subtype_of_repr,
                    vman,
                ));
                let exp2_rep = BaseValueDomain::from(self.evaluate_expression(
                    exp_rhs,
                    defining_tvars_are_subtype_of_repr,
                    vman,
                ));
                let nvar = DerivedTypeVar::new(vman.fresh());
                exp1_repr
                    .merge(exp2_rep, &|lhs, rhs, mut cons| {
                        let add_const = AddConstraint::new(lhs, rhs, nvar.clone());
                        cons.insert(TyConstraint::AddCons(add_const));
                        BaseValueDomain {
                            repr_var: nvar.clone(),
                            additional_constriants: cons,
                        }
                    })
                    .into()
            }
        }
    }

    fn is_constant_one(expr: &Expression) -> bool {
        match expr {
            Expression::Const(ap) => ap.is_one(),
            _ => false,
        }
    }

    fn evaluate_binop(
        &self,
        op: &BinOpType,
        lhs: &Expression,
        rhs: &Expression,
        defining_tvars_are_subtype_of_repr: bool,
        vman: &mut VariableManager,
    ) -> (DerivedTypeVar, ConstraintSet) {
        match op {
            // TODO(Ian): Think about this case a bit more
            // Should probably at a minimum propogate something to the operands
            BinOpType::IntMult => {
                if Self::is_constant_one(lhs) {
                    self.evaluate_expression(rhs, defining_tvars_are_subtype_of_repr, vman)
                } else if Self::is_constant_one(rhs) {
                    self.evaluate_expression(lhs, defining_tvars_are_subtype_of_repr, vman)
                } else {
                    self.assume_weak_integral(vman)
                }
            }
            BinOpType::IntAdd => self.eval_add(lhs, rhs, defining_tvars_are_subtype_of_repr, vman),
            BinOpType::IntSub => self.eval_add(
                lhs,
                &Expression::UnOp {
                    op: UnOpType::IntNegate,
                    arg: Box::new(rhs.clone()),
                },
                defining_tvars_are_subtype_of_repr,
                vman,
            ),
            _ => {
                let repr = vman.fresh();
                warn!("Unhandled binop type: {:?}, representing with {}", op, repr);
                (DerivedTypeVar::new(repr), ConstraintSet::default())
            }
        }
    }

    fn unhandled_expr(
        value: &Expression,
        vman: &mut VariableManager,
    ) -> (DerivedTypeVar, ConstraintSet) {
        let repr = vman.fresh();
        warn!(
            "Unhandled expression: {:?} representing with {}",
            value, repr
        );
        (DerivedTypeVar::new(repr), ConstraintSet::empty())
    }

    fn assume_weak_integral(&self, vman: &mut VariableManager) -> (DerivedTypeVar, ConstraintSet) {
        // we dont know the exact type of the expr but we know it's at least subtype of a weak int
        let f = vman.fresh();
        let dtv = DerivedTypeVar::new(f);
        let mut cs = ConstraintSet::default();
        cs.insert(TyConstraint::SubTy(SubtypeConstraint {
            lhs: dtv.clone(),
            rhs: DerivedTypeVar::new(self.weakest_integral_type.clone()),
        }));
        (dtv, cs)
    }

    fn evaluate_expression(
        &self,
        value: &Expression,
        defining_tvars_are_subtype_of_repr: bool,
        vman: &mut VariableManager,
    ) -> (DerivedTypeVar, ConstraintSet) {
        if let Some(gvar) = self
            .points_to
            .get_pointer_variable(value, &self.constant_resolver)
        {
            return (gvar, ConstraintSet::default());
        }

        match &value {
            Expression::Var(v2) => {
                let vars = self.reg_map.access(v2);
                if vars.len() == 1 {
                    let repr = vars.into_iter().next().unwrap();
                    (DerivedTypeVar::new(repr), ConstraintSet::default())
                } else if vars.is_empty() {
                    (DerivedTypeVar::new(vman.fresh()), ConstraintSet::default())
                } else {
                    let repr = DerivedTypeVar::new(vman.fresh());
                    let cons: BTreeSet<TyConstraint> = vars
                        .into_iter()
                        .map(|def_var| {
                            if defining_tvars_are_subtype_of_repr {
                                TyConstraint::SubTy(SubtypeConstraint::new(
                                    DerivedTypeVar::new(def_var),
                                    repr.clone(),
                                ))
                            } else {
                                TyConstraint::SubTy(SubtypeConstraint::new(
                                    repr.clone(),
                                    DerivedTypeVar::new(def_var),
                                ))
                            }
                        })
                        .collect();

                    (repr, ConstraintSet::from(cons))
                }
            }
            Expression::BinOp { op, lhs, rhs } => {
                self.evaluate_binop(op, lhs, rhs, defining_tvars_are_subtype_of_repr, vman)
            }
            Expression::Cast {
                op,
                size: _,
                arg: _,
            } => match op {
                cwe_checker_lib::intermediate_representation::CastOpType::IntZExt => {
                    self.assume_weak_integral(vman)
                }
                cwe_checker_lib::intermediate_representation::CastOpType::IntSExt => {
                    self.assume_weak_integral(vman)
                }
                cwe_checker_lib::intermediate_representation::CastOpType::Int2Float => {
                    Self::unhandled_expr(value, vman)
                }
                cwe_checker_lib::intermediate_representation::CastOpType::Float2Float => {
                    Self::unhandled_expr(value, vman)
                }
                cwe_checker_lib::intermediate_representation::CastOpType::Trunc => {
                    self.assume_weak_integral(vman)
                }
                cwe_checker_lib::intermediate_representation::CastOpType::PopCount => {
                    Self::unhandled_expr(value, vman)
                }
            },
            Expression::Const(value) => (
                self.constant_resolver
                    .resolve_constant_to_variable(value, vman),
                ConstraintSet::default(),
            ),
            _ => Self::unhandled_expr(value, vman), // TODO(ian) handle additional constraints, add/sub
        }
    }

    fn apply_assign(
        &self,
        tid: &Tid,
        var: &Variable,
        value: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        info!("Working on tid {}", tid);
        info!("Assigning {:?} to {:?}", value, var);
        let (value_type_var, mut constraints) = self.evaluate_expression(value, true, vman);
        info!("{}", value_type_var);
        for repr_cons in constraints.iter() {
            info!("{}", repr_cons);
        }

        let cons = Self::reg_update(tid, var, value_type_var);
        constraints.insert_all(&cons);
        constraints
    }

    fn reg_update(at_term: &Tid, v_into: &Variable, value_repr: DerivedTypeVar) -> ConstraintSet {
        let reg_tv = tid_indexed_by_variable(at_term, v_into);
        let mut cons = ConstraintSet::default();
        cons.insert(TyConstraint::SubTy(SubtypeConstraint::new(
            value_repr,
            DerivedTypeVar::new(reg_tv),
        )));
        cons
    }

    fn apply_load(
        &self,
        tid: &Tid,
        v_into: &Variable,
        address: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let bv = self.memaccess(address, v_into.size, vman);

        let cons = bv.additional_constriants;
        let addr_repr = bv.repr_var;

        let mut base_set = Self::reg_update(tid, v_into, addr_repr);
        base_set.insert_all(&cons);
        base_set
    }

    fn build_addressing_representation(
        &self,
        adressing_expr: &Expression,
        sz: ByteSize,
        field_label: FieldLabel,
        address_is_subtype: bool,
        vman: &mut VariableManager,
    ) -> BaseValueDomain {
        let tv_access = self.points_to.points_to(adressing_expr, sz);
        let (reg_repr, mut cons) =
            self.evaluate_expression(adressing_expr, !address_is_subtype, vman);

        let mut representation = reg_repr;
        representation.add_field_label(field_label);
        representation.add_field_label(FieldLabel::Field(Field::new(0, sz.as_bit_length())));

        representation = simplify_path(&representation);

        for acc in tv_access.iter() {
            if let Some(off) = acc.offset {
                let mut dt_repr = DerivedTypeVar::new(acc.ty_var.clone());

                dt_repr.add_field_label(FieldLabel::Field(Field::new(off, acc.sz.as_bit_length())));

                let new_cons = if address_is_subtype {
                    SubtypeConstraint::new(representation.clone(), dt_repr)
                } else {
                    SubtypeConstraint::new(dt_repr, representation.clone())
                };
                cons.insert(TyConstraint::SubTy(new_cons));
            }
        }

        BaseValueDomain {
            repr_var: representation,
            additional_constriants: cons,
        }
    }

    fn memaccess(
        &self,
        adressing_expr: &Expression,
        sz: ByteSize,
        vman: &mut VariableManager,
    ) -> BaseValueDomain {
        self.build_addressing_representation(adressing_expr, sz, FieldLabel::Load, false, vman)
    }

    /// A memupdate is side effectings so has no repr
    fn memupdate(
        &self,
        addressing_expr: &Expression,
        value_expr: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        info!("Addressing: {:?}", addressing_expr);
        let bv_dom = self.build_addressing_representation(
            addressing_expr,
            value_expr.bytesize(),
            FieldLabel::Store,
            true,
            vman,
        );

        let mut cons = bv_dom.additional_constriants;

        cons.iter().for_each(|x| {
            if let TyConstraint::SubTy(sy) = x {
                info!("update cons {}", sy);
            }
        });

        let ptr_repr = bv_dom.repr_var;

        let (value_repr, value_cons) = self.evaluate_expression(value_expr, true, vman);

        cons.insert_all(&value_cons);

        cons.insert(TyConstraint::SubTy(SubtypeConstraint::new(
            value_repr, ptr_repr,
        )));

        cons
    }

    fn apply_store(
        &self,
        tid: &Tid,
        value_from: &Expression,
        address_into: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        self.memupdate(address_into, value_from, vman)
    }

    fn handle_def(&self, df: &Term<Def>, vman: &mut VariableManager) -> ConstraintSet {
        match &df.term {
            Def::Load { var, address } => self.apply_load(&df.tid, var, address, vman),
            Def::Store { address, value } => self.apply_store(&df.tid, value, address, vman),
            Def::Assign { var, value } => self.apply_assign(&df.tid, var, value, vman),
        }
    }

    fn argtvar_to_dtv(tvar: ArgTvar, displacement: i64) -> DerivedTypeVar {
        match tvar {
            ArgTvar::VariableTvar(tv) => DerivedTypeVar::new(tv),
            ArgTvar::MemTvar(tv_access) => {
                let mut dt = DerivedTypeVar::new(tv_access.ty_var);

                if let Some(off) = tv_access.offset {
                    dt.add_field_label(FieldLabel::Field(Field::new(
                        off + displacement,
                        tv_access.sz.as_bit_length(),
                    )));
                }
                dt
            }
        }
    }

    fn create_formal_tvar<T>(
        calling_blk: Option<&Term<Blk>>,
        indx: usize,
        index_to_field_label: &impl Fn(usize) -> FieldLabel,
        sub: &Term<T>,
    ) -> DerivedTypeVar {
        let base_tv = if let Some(tg) = calling_blk {
            term_to_tvar_with_tag(sub, tg)
        } else {
            term_to_tvar(sub)
        };

        let mut base = DerivedTypeVar::new(base_tv);
        base.add_field_label(index_to_field_label(indx));
        base
    }

    fn make_constraints<T>(
        &self,
        callsite: SubprocedureInvocation<T>,
        index_to_field_label: &impl Fn(usize) -> FieldLabel,
        arg_is_written: bool,
        displacement: i64,
        vm: &mut VariableManager,
    ) -> ConstraintSet {
        let mut start_constraints = ConstraintSet::default();
        for (i, arg) in callsite.args.iter().enumerate() {
            let formal_tv = Self::create_formal_tvar(
                callsite.calling_blk,
                i,
                index_to_field_label,
                callsite.sub,
            );
            let arg_tvars = self
                .subprocedure_locators
                .get_type_variables_and_constraints_for_arg(
                    arg,
                    &self.reg_map,
                    &self.points_to,
                    vm,
                );

            for arg_repr_tvar in arg_tvars {
                let dt = Self::argtvar_to_dtv(arg_repr_tvar, displacement);
                let new_cons = if arg_is_written {
                    SubtypeConstraint::new(formal_tv.clone(), dt)
                } else {
                    SubtypeConstraint::new(dt, formal_tv.clone())
                };
                start_constraints.insert(TyConstraint::SubTy(new_cons));
            }
        }
        start_constraints
    }

    /// make each formal the subtype of the addressing info for this parameter within the current state
    fn handle_entry_formals(&self, sub: &Term<Sub>, vman: &mut VariableManager) -> ConstraintSet {
        info!(
            "Proc: {} has formals: {}",
            sub.tid,
            sub.term.formal_args.len()
        );
        self.make_constraints(
            SubprocedureInvocation {
                calling_blk: None,
                sub,
                args: &sub.term.formal_args,
            },
            &FieldLabel::In,
            true,
            0,
            vman,
        )
    }

    /// make each formal the subtype of the addressing info for this parameter within the current state
    fn handle_return_formals(&self, sub: &Term<Sub>, vman: &mut VariableManager) -> ConstraintSet {
        self.make_constraints(
            SubprocedureInvocation {
                calling_blk: None,
                sub,
                args: &sub.term.formal_rets,
            },
            &FieldLabel::Out,
            false,
            0,
            vman,
        )
    }

    /*
    So the actuals are displaced by the stored return address since args are marked by the the displacement after the CALL, need to adjust by address size back.
    */

    fn handle_return_actual(
        &self,
        calling_blk: &Term<Blk>,
        sub: &Term<Sub>,
        vman: &mut VariableManager,
        return_address_displacement: i64,
    ) -> ConstraintSet {
        self.make_constraints(
            SubprocedureInvocation {
                calling_blk: Some(calling_blk),
                sub,
                args: &sub.term.formal_rets,
            },
            &FieldLabel::Out,
            true,
            return_address_displacement,
            vman,
        )
    }

    //TODO(Ian): implement callsite cloning
    fn handle_call_actual(
        &self,
        calling_blk: &Term<Blk>,
        sub: &Term<Sub>,
        vman: &mut VariableManager,
        return_address_displacement: i64,
    ) -> ConstraintSet {
        self.make_constraints(
            SubprocedureInvocation {
                calling_blk: Some(calling_blk),
                sub,
                args: &sub.term.formal_args,
            },
            &FieldLabel::In,
            false,
            return_address_displacement,
            vman,
        )
    }

    fn handle_extern_actual_params(
        &self,
        calling_blk: &Term<Blk>,
        sub: &Term<ExternSymbol>,
        vman: &mut VariableManager,
        return_address_displacement: i64,
    ) -> ConstraintSet {
        self.make_constraints(
            SubprocedureInvocation {
                calling_blk: Some(calling_blk),
                sub,
                args: &sub.term.parameters,
            },
            &FieldLabel::In,
            false,
            return_address_displacement,
            vman,
        )
    }

    fn handle_extern_actual_rets(
        &self,
        calling_blk: &Term<Blk>,
        sub: &Term<ExternSymbol>,
        vman: &mut VariableManager,
        return_address_displacement: i64,
    ) -> ConstraintSet {
        self.make_constraints(
            SubprocedureInvocation {
                calling_blk: Some(calling_blk),
                sub,
                args: &sub.term.return_values,
            },
            &FieldLabel::Out,
            true,
            return_address_displacement,
            vman,
        )
    }
}

/// Thread the blk context through an inner state computation, monad like.
pub fn fold_over_definition_states<C: NodeContextMapping, I>(
    nd_ctxt: C,
    blk: &Term<Blk>,
    init_inner_state: I,
    produce_new_inner_state: &mut impl FnMut(&Term<Def>, &C, I) -> I,
) -> I {
    let (final_inner_state, _last_nd_ctxt) = blk.term.defs.iter().fold(
        (init_inner_state, nd_ctxt),
        |(inner_state, new_ctxt), df: &Term<Def>| {
            let next_inner = produce_new_inner_state(df, &new_ctxt, inner_state);
            let next_ctxt = new_ctxt.apply_def(df);

            (next_inner, next_ctxt)
        },
    );

    final_inner_state
}

/// Holds a mapping between the nodes and their flow-sensitive analysis results, which
/// are needed for constraint generation
pub struct Context<'a, R, P, S, C>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    C: ConstantResolver,
{
    graph: &'a Graph<'a>,
    node_contexts: &'a HashMap<NodeIndex, NodeContext<R, P, S, C>>,
    extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
    function_filter: Option<HashSet<Tid>>,
}

impl<'a, R, P, S, C> Context<'a, R, P, S, C>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    C: ConstantResolver,
{
    /// Creates a new context for type constraint generation.
    pub fn new(
        graph: &'a Graph<'a>,
        node_contexts: &'a HashMap<NodeIndex, NodeContext<R, P, S, C>>,
        extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
        function_filter: Option<HashSet<Tid>>,
    ) -> Context<'a, R, P, S, C> {
        Context {
            graph,
            node_contexts,
            extern_symbols,
            function_filter,
        }
    }

    fn blk_does_return(blk: &Term<Blk>) -> bool {
        blk.term
            .jmps
            .iter()
            .any(|jmp| matches!(jmp.term, Jmp::Return(_)))
    }

    fn handle_block_start(
        nd_ctxt: NodeContext<R, P, S, C>,
        blk: &Term<Blk>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        info!("Starting block {}", blk.tid);
        blk.term
            .defs
            .iter()
            .for_each(|x| info!("Has {} {:?}", x.tid, x.term));
        fold_over_definition_states(
            nd_ctxt,
            blk,
            ConstraintSet::default(),
            &mut |df: &Term<Def>,
                  curr_ctxt: &NodeContext<R, P, S, C>,
                  mut curr_constraints: ConstraintSet| {
                curr_constraints.insert_all(&curr_ctxt.handle_def(df, vman));
                curr_constraints
            },
        )
    }

    /* Adjusting stack displacement for actuals is not nessecary since the stack is computed as the maximum depth which will include the return address
    TODO(ian): verify this
    fn get_return_address_displacement(&self) -> i64 {
        let res: i64 = (self.type_properties.pointer_size.as_bit_length() / 8)
            .try_into()
            .expect("stack displacement should be small enough");
        -res
    }
    */
    fn collect_extern_call_constraints(
        &self,
        calling_blk: &Term<Blk>,
        nd_ctxt: &NodeContext<R, P, S, C>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let edges = &calling_blk.term.jmps;
        let called_externs = edges.iter().filter_map(|jmp| {
            if let Jmp::Call { target, .. } = &jmp.term {
                return self.extern_symbols.get(target).map(|t| Term {
                    term: t.clone(),
                    tid: target.clone(),
                });
            }

            None
        });

        called_externs
            .into_iter()
            .map(|ext| nd_ctxt.handle_extern_actual_params(calling_blk, &ext, vman, 0))
            .fold(ConstraintSet::default(), |mut prev, nxt| {
                prev.insert_all(&nxt);
                prev
            })
    }

    fn collect_extern_ret_constraints(
        &self,
        nd_ind: NodeIndex,
        nd_ctxt: &NodeContext<R, P, S, C>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let mut cons = ConstraintSet::default();
        for edge in self.graph.edges_directed(nd_ind, EdgeDirection::Outgoing) {
            let source_node: Node = self.graph[edge.source()];
            if let Edge::ExternCallStub(jmp) = edge.weight() {
                if let Jmp::Call { target, .. } = &jmp.term {
                    if let Some(extern_symb) = self.extern_symbols.get(target) {
                        let term = Term {
                            term: extern_symb.clone(),
                            tid: target.clone(),
                        };
                        // Calls to externs  should go from blocks to blocks
                        assert!(matches!(source_node, Node::BlkEnd(_, _)));
                        if let Node::BlkEnd(blk, _) = source_node {
                            cons.insert_all(
                                &nd_ctxt.handle_extern_actual_rets(blk, &term, vman, 0),
                            );
                        }
                    }
                }
            }
        }
        cons
    }

    fn get_func_tid(&self, nd: Node) -> Tid {
        match nd {
            Node::BlkStart(_blk, sub) => &sub.tid,
            Node::CallReturn {
                call: (_call_blk, calling_proc),
                return_: (_returned_to_blk, _return_proc),
            } => &calling_proc.tid,
            Node::CallSource {
                source: (_source_blk, source_func),
                target: (_target_blk, _target_func),
            } => &source_func.tid,
            // block post conditions arent needed to generate constraints
            Node::BlkEnd(_blk, sub) => &sub.tid,
        }
        .clone()
    }

    fn should_generate_for_block(&self, nd: Node) -> bool {
        self.function_filter
            .as_ref()
            .map(|funcs| funcs.contains(&self.get_func_tid(nd)))
            .unwrap_or(true)
    }

    fn generate_constraints_for_node(
        &self,
        nd_ind: NodeIndex,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let nd_cont = self.node_contexts.get(&nd_ind);
        let nd = self.graph[nd_ind];
        if !self.should_generate_for_block(nd) {
            return ConstraintSet::default();
        }

        if let Some(nd_cont) = nd_cont {
            match nd {
                Node::BlkStart(blk, sub) => {
                    // TODO(ian): if there is an incoming extern call then we need to add the extern actual rets

                    let mut total_cons = ConstraintSet::default();

                    info!("Collecting extern constraints for {} {}", sub.tid, blk.tid);
                    let add_cons = self.collect_extern_ret_constraints(nd_ind, nd_cont, vman);

                    info!("Cons extern: {}", add_cons);
                    total_cons.insert_all(&add_cons);

                    if blk.tid == sub.term.blocks[0].tid {
                        let ent_cons = nd_cont.handle_entry_formals(sub, vman);
                        info!("entry formals, {:?}", ent_cons);
                        total_cons.insert_all(&ent_cons);
                    }
                    let new_context: NodeContext<R, P, S, C> = (*nd_cont).clone();
                    total_cons.insert_all(&Self::handle_block_start(new_context, blk, vman));
                    total_cons
                }
                Node::CallReturn {
                    call: (call_blk, calling_proc),
                    return_: (return_from_block, return_proc),
                } => {
                    info!(
                        "Call-return caller: {}, return {}",
                        calling_proc.tid, return_proc.tid
                    );

                    // We want to apply return actuals after the def of ths return has been applied in the nd_context
                    // Could do this on blk start maybe, incoming edges type thing

                    let mut total_cons = ConstraintSet::default();
                    //for e in self.graph.edges_directed(nd_ind, EdgeDirection::Outgoing) {
                    //    let tgt = e.target();

                    //  let post_cond = nd_cont.apply_return();

                    for e in self
                        .graph
                        .edges_directed(nd_ind, EdgeDirection::Outgoing)
                        .filter(|x| self.should_generate_for_block(self.graph[x.target()]))
                    {
                        // Call Return should always have a single return combine
                        match e.weight() {
                            Edge::ReturnCombine(call_site) => {
                                let post_cond = nd_cont
                                    .apply_return_node(call_site, &return_from_block.term.jmps[0]);
                                total_cons.insert_all(&post_cond.handle_return_actual(
                                    call_blk,
                                    return_proc,
                                    vman,
                                    0,
                                ));
                            }
                            _ => panic!("Malformed CFG"),
                        }
                    }

                    total_cons
                }
                Node::CallSource {
                    source: (source_blk, _src_func),
                    target: (_called_blk, target_func),
                } => nd_cont.handle_call_actual(source_blk, target_func, vman, 0),
                // block post conditions arent needed to generate constraints
                Node::BlkEnd(blk, sub) => {
                    let mut cs = ConstraintSet::default();

                    let add_cons = self.collect_extern_call_constraints(blk, nd_cont, vman);
                    info!("Extern cons: {}\n", add_cons);
                    cs.insert_all(&add_cons);

                    // TODO(ian): if there is an outgoing extern call then we need to add the actual args
                    if Self::blk_does_return(blk) {
                        info!("Handling formals: {}", sub.tid);
                        cs.insert_all(&nd_cont.handle_return_formals(sub, vman));
                    }

                    cs
                }
            }
        } else {
            ConstraintSet::default()
        }
    }

    /// Walks all of the nodes and gather the inferred subtyping constraints.
    pub fn generate_constraints(&self, vman: &mut VariableManager) -> ConstraintSet {
        let mut cs: ConstraintSet = Default::default();
        for nd_ind in self.graph.node_indices() {
            cs = ConstraintSet::from(
                cs.union(&self.generate_constraints_for_node(nd_ind, vman))
                    .cloned()
                    .collect::<BTreeSet<TyConstraint>>(),
            );
        }
        cs
    }
}
