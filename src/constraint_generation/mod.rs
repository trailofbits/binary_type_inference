use cwe_checker_lib::{
    analysis::graph::{Graph, Node},
    intermediate_representation::{Arg, Blk, Def, Sub, Term},
};
use log::warn;
use petgraph::graph::NodeIndex;

use cwe_checker_lib::intermediate_representation::{ByteSize, Expression, Variable};

use cwe_checker_lib::intermediate_representation::Tid;

use crate::constraints::{
    ConstraintSet, DerivedTypeVar, Field, FieldLabel, SubtypeConstraint, TypeVariable,
    VariableManager,
};

use log::error;
use std::collections::{btree_set::BTreeSet, HashMap};

/// Gets a type variable for a [Tid] where multiple type variables need to exist at that [Tid] which are distinguished by which [Variable] they operate over.
pub fn tid_indexed_by_variable(tid: &Tid, var: &Variable) -> TypeVariable {
    TypeVariable::new(tid.get_str_repr().to_owned() + "_" + &var.name)
}

/// Converts a [Tid] to a [TypeVariable] by retrieving the string representation of the TID
pub fn tid_to_tvar(tid: &Tid) -> TypeVariable {
    TypeVariable::new(tid.get_str_repr().to_owned())
}

/// Converts a term to a TypeVariable by using its unique term identifier (Tid).
pub fn term_to_tvar<T>(term: &Term<T>) -> TypeVariable {
    tid_to_tvar(&term.tid)
}

/// Creates an actual argument type variable for the procedure
pub fn arg_tvar(index: usize, target_sub: &Tid) -> TypeVariable {
    TypeVariable::new(format!("arg_{}_{}", target_sub.get_str_repr(), index))
}

/// Maps a variable (register) to it's representing type variable at this time step in the program. This type variable is some representation of
/// all reaching definitions of this register.
pub trait RegisterMapping {
    /// Creates or returns the type variable representing this register at this program point. Takes a [VariableManager] so it
    /// can create fresh type variables.
    fn access(&self, var: &Variable, vman: &mut VariableManager) -> (TypeVariable, ConstraintSet);
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
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
pub trait PointsToMapping {
    /// Gets the set of type variables this address expression points to.  Takes a [VariableManager] so it
    /// can create fresh type variables.
    fn points_to(
        &self,
        address: &Expression,
        sz: ByteSize,
        vman: &mut VariableManager,
    ) -> BTreeSet<TypeVariableAccess>;
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
pub trait SubprocedureLocators {
    // TODO(ian) may need the subprocedure tid here.
    /// Takes a points-to and register mapping to resolve type variables of inputs and outputs
    fn get_type_variables_and_constraints_for_arg(
        &self,
        arg: &Arg,
        reg: &impl RegisterMapping,
        points_to: &impl PointsToMapping,
        vm: &mut VariableManager,
    ) -> (BTreeSet<ArgTvar>, ConstraintSet);
}

/// Represents the flow-sensitive context needed by flow-insensitive constraint generation to generate type variables and constraints at a given program point.
/// The register mapping provides constraints and type variables to represent a register when it is accessed via some notion of reaching definitions.
/// The PointsToMapping determines the set of a type variables a load or store points to in order to generate constraints.
/// Finally the SubprocedureLocators are used to link actual and formal arguments and returns within constraints.
pub struct NodeContext<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators> {
    reg_map: R,
    points_to: P,
    subprocedure_locators: S,
}

impl<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators> NodeContext<R, P, S> {
    /// Given a register, pointer, and subprocedure mapping, generates a full NodeContext.
    pub fn new(r: R, p: P, s: S) -> NodeContext<R, P, S> {
        NodeContext {
            reg_map: r,
            points_to: p,
            subprocedure_locators: s,
        }
    }

    fn evaluate_expression(
        &self,
        value: &Expression,
        vman: &mut VariableManager,
    ) -> (TypeVariable, ConstraintSet) {
        match &value {
            Expression::Var(v2) => {
                let (rhs_type_var, additional_constraints) = self.reg_map.access(v2, vman);
                (rhs_type_var, additional_constraints)
            }
            _ => {
                warn!("Unhandled expression: {:?}", value);
                (vman.fresh(), ConstraintSet::empty())
            } // TODO(ian) handle additional constraints, add/sub
        }
    }

    fn generate_expression_constraint(
        &self,
        lhs_type_var: TypeVariable,
        value: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let (rhs_type_var, mut constraints) = self.evaluate_expression(value, vman);
        constraints.insert(SubtypeConstraint::new(
            DerivedTypeVar::new(rhs_type_var),
            DerivedTypeVar::new(lhs_type_var),
        ));
        constraints
    }

    fn apply_assign(
        &self,
        tid: &Tid,
        var: &Variable,
        value: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let mut constraints = ConstraintSet::default();
        let typ_var = tid_indexed_by_variable(tid, var);
        let new_cons = self.generate_expression_constraint(typ_var, value, vman);
        constraints.insert_all(&new_cons);
        constraints
    }

    fn make_mem_tvar(var: TypeVariableAccess, label: FieldLabel) -> DerivedTypeVar {
        let mut der_var = DerivedTypeVar::new(var.ty_var);
        der_var.add_field_label(label);
        if let Some(off) = var.offset {
            der_var.add_field_label(FieldLabel::Field(Field::new(off, var.sz.as_bit_length())));
        }
        der_var
    }
    fn make_loaded_tvar(var: TypeVariableAccess) -> DerivedTypeVar {
        Self::make_mem_tvar(var, FieldLabel::Load)
    }

    fn apply_load(
        &self,
        tid: &Tid,
        v_into: &Variable,
        address: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let constraints = ConstraintSet::default();
        let typ_var = tid_indexed_by_variable(tid, v_into);
        self.apply_mem_op(
            typ_var,
            constraints,
            &Expression::Var(v_into.clone()),
            address,
            vman,
            Self::make_loaded_tvar,
            true,
        )
    }

    fn make_store_tvar(var: TypeVariableAccess) -> DerivedTypeVar {
        Self::make_mem_tvar(var, FieldLabel::Store)
    }

    fn apply_mem_op(
        &self,
        reg_value: TypeVariable,
        mut reg_constraints: ConstraintSet,
        reg_expr: &Expression,
        address: &Expression,
        vman: &mut VariableManager,
        make_type_var: impl Fn(TypeVariableAccess) -> DerivedTypeVar,
        memop_is_upcasted: bool,
    ) -> ConstraintSet {
        let all_tvars = self.points_to.points_to(address, reg_expr.bytesize(), vman);
        let all_dtvars: BTreeSet<DerivedTypeVar> =
            all_tvars.into_iter().map(|tv| make_type_var(tv)).collect();

        all_dtvars
            .into_iter()
            .map(|memop_tvar| {
                let reg_tvar = DerivedTypeVar::new(reg_value.clone());
                if memop_is_upcasted {
                    SubtypeConstraint::new(memop_tvar, reg_tvar)
                } else {
                    SubtypeConstraint::new(reg_tvar, memop_tvar)
                }
            })
            .for_each(|cons| {
                reg_constraints.insert(cons);
            });
        reg_constraints
    }

    fn apply_store(
        &self,
        tid: &Tid,
        value_from: &Expression,
        address_into: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let (reg_val, constraints) = self.evaluate_expression(value_from, vman);
        self.apply_mem_op(
            reg_val,
            constraints,
            value_from,
            address_into,
            vman,
            Self::make_store_tvar,
            false,
        )
    }

    fn handle_def(&self, df: &Term<Def>, vman: &mut VariableManager) -> ConstraintSet {
        match &df.term {
            Def::Load { var, address } => self.apply_load(&df.tid, var, address, vman),
            Def::Store { address, value } => self.apply_store(&df.tid, value, address, vman),
            Def::Assign { var, value } => self.apply_assign(&df.tid, var, value, vman),
        }
    }

    fn handle_block_start(&self, blk: &Term<Blk>, vman: &mut VariableManager) -> ConstraintSet {
        blk.term
            .defs
            .iter()
            .map(|df: &Term<Def>| self.handle_def(df, vman))
            .fold(ConstraintSet::default(), |x, y| {
                ConstraintSet::from(
                    x.union(&y)
                        .cloned()
                        .collect::<BTreeSet<SubtypeConstraint>>(),
                )
            })
    }

    fn argtvar_to_dtv(tvar: ArgTvar) -> DerivedTypeVar {
        match tvar {
            ArgTvar::VariableTvar(tv) => DerivedTypeVar::new(tv),
            ArgTvar::MemTvar(tv_access) => Self::make_loaded_tvar(tv_access),
        }
    }

    fn arg_to_constraints(
        &self,
        target_func: &Term<Sub>,
        ind: usize,
        arg: &Arg,
        vm: &mut VariableManager,
        index_to_field_label: &impl Fn(usize) -> FieldLabel,
        arg_is_subtype_of_representations: bool,
    ) -> ConstraintSet {
        let mut base_var = DerivedTypeVar::new(term_to_tvar(target_func));
        base_var.add_field_label(index_to_field_label(ind));
        let (type_vars_for_arg, mut additional_constraints) = self
            .subprocedure_locators
            .get_type_variables_and_constraints_for_arg(arg, &self.reg_map, &self.points_to, vm);
        type_vars_for_arg
            .into_iter()
            .map(|tvar| {
                if arg_is_subtype_of_representations {
                    SubtypeConstraint::new(base_var.clone(), Self::argtvar_to_dtv(tvar))
                } else {
                    SubtypeConstraint::new(Self::argtvar_to_dtv(tvar), base_var.clone())
                }
            })
            .for_each(|cons| {
                additional_constraints.insert(cons);
            });
        additional_constraints
    }

    fn handle_call(&self, target_function: &Term<Sub>, vm: &mut VariableManager) -> ConstraintSet {
        self.handle_function_args(
            target_function,
            &target_function.term.formal_args,
            vm,
            &|ind| FieldLabel::In(ind),
            false,
        )
    }

    fn handle_function_args(
        &self,
        target_function: &Term<Sub>,
        args: &[Arg],
        vm: &mut VariableManager,
        index_to_field_label: &impl Fn(usize) -> FieldLabel,
        arg_is_subtype_of_representations: bool,
    ) -> ConstraintSet {
        let mut constraints = ConstraintSet::default();
        args.iter()
            .enumerate()
            .map(|(ind, arg)| {
                self.arg_to_constraints(
                    target_function,
                    ind,
                    arg,
                    vm,
                    index_to_field_label,
                    arg_is_subtype_of_representations,
                )
            })
            .for_each(|cons| constraints.insert_all(&cons));
        constraints
    }

    fn handle_return(&self, return_from: &Term<Sub>, vm: &mut VariableManager) -> ConstraintSet {
        self.handle_function_args(
            return_from,
            &return_from.term.formal_rets,
            vm,
            &|ind| FieldLabel::Out(ind),
            true,
        )
    }
}

/// Holds a mapping between the nodes and their flow-sensitive analysis results, which
/// are needed for constraint generation
pub struct Context<'a, R, P, S>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    graph: &'a Graph<'a>,
    node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
}

impl<'a, R, P, S> Context<'a, R, P, S>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    /// Creates a new context for type constraint generation.
    pub fn new(
        graph: &'a Graph<'a>,
        node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
    ) -> Context<'a, R, P, S> {
        Context {
            graph,
            node_contexts,
        }
    }

    fn generate_constraints_for_node(
        &self,
        nd_ind: NodeIndex,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let nd_cont = self.node_contexts.get(&nd_ind);
        let nd = self.graph[nd_ind];

        if let Some(nd_cont) = nd_cont {
            match nd {
                Node::BlkStart(blk, _sub) => nd_cont.handle_block_start(blk, vman),
                Node::CallReturn {
                    call: _call,
                    return_: (_returned_to_blk, return_proc),
                } => nd_cont.handle_return(return_proc, vman),
                Node::CallSource {
                    source: _source,
                    target: (_calling_blk, target_func),
                } => nd_cont.handle_call(target_func, vman),
                // block post conditions arent needed to generate constraints
                Node::BlkEnd(_blk, _term) => Default::default(),
            }
        } else {
            ConstraintSet::default()
        }
    }

    /// Walks all of the nodes and gather the inferred subtyping constraints.
    pub fn generate_constraints(&self) -> ConstraintSet {
        let mut vman = VariableManager::new();
        let mut cs: ConstraintSet = Default::default();
        for nd_ind in self.graph.node_indices() {
            cs = ConstraintSet::from(
                cs.union(&self.generate_constraints_for_node(nd_ind, &mut vman))
                    .cloned()
                    .collect::<BTreeSet<SubtypeConstraint>>(),
            );
        }
        cs
    }
}
