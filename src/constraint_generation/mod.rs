use cwe_checker_lib::{
    analysis::graph::{Edge, Graph, Node},
    intermediate_representation::{Arg, Blk, Def, ExternSymbol, Jmp, Sub, Term},
};
use log::{info, warn};
use petgraph::{
    graph::{Edges, IndexType, NodeIndex},
    visit::IntoEdges,
    EdgeDirection, EdgeType,
};

use cwe_checker_lib::intermediate_representation::{ByteSize, Expression, Variable};

use cwe_checker_lib::intermediate_representation::Tid;

use crate::constraints::{
    ConstraintSet, DerivedTypeVar, Field, FieldLabel, SubtypeConstraint, TypeVariable,
    VariableManager,
};

use std::{
    collections::{btree_set::BTreeSet, BTreeMap, HashMap},
    hash::Hash,
};

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

pub trait NodeContextMapping: Clone {
    fn apply_def(&self, term: &Term<Def>) -> Self;
}

/// Maps a variable (register) to it's representing type variable at this time step in the program. This type variable is some representation of
/// all reaching definitions of this register.
pub trait RegisterMapping: NodeContextMapping {
    /// Creates or returns the type variable representing this register at this program point. Takes a [VariableManager] so it
    /// can create fresh type variables.
    fn access(&self, var: &Variable, vman: &mut VariableManager) -> (TypeVariable, ConstraintSet);
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

struct Memop {
    sz: ByteSize,
    addr: Expression,
    reg_value: TypeVariable,
    reg_constraints: ConstraintSet,
}

impl Memop {
    fn apply_mem_op(
        &self,
        points_to: &impl PointsToMapping,
        vman: &mut VariableManager,
        make_type_var: impl Fn(TypeVariableAccess) -> DerivedTypeVar,
        memop_is_upcasted: bool,
    ) -> ConstraintSet {
        let mut new_cons = self.reg_constraints.clone();
        let all_tvars = points_to.points_to(&self.addr, self.sz, vman);
        let all_dtvars: BTreeSet<DerivedTypeVar> =
            all_tvars.into_iter().map(|tv| make_type_var(tv)).collect();

        all_dtvars
            .into_iter()
            .map(|memop_tvar| {
                let reg_tvar = DerivedTypeVar::new(self.reg_value.clone());
                if memop_is_upcasted {
                    SubtypeConstraint::new(memop_tvar, reg_tvar)
                } else {
                    SubtypeConstraint::new(reg_tvar, memop_tvar)
                }
            })
            .for_each(|cons| {
                info!("{}", cons);
                new_cons.insert(cons);
            });
        ConstraintSet::from(new_cons)
    }
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
    ) -> (BTreeSet<ArgTvar>, ConstraintSet);
}

/// Represents the flow-sensitive context needed by flow-insensitive constraint generation to generate type variables and constraints at a given program point.
/// The register mapping provides constraints and type variables to represent a register when it is accessed via some notion of reaching definitions.
/// The PointsToMapping determines the set of a type variables a load or store points to in order to generate constraints.
/// Finally the SubprocedureLocators are used to link actual and formal arguments and returns within constraints.
#[derive(Clone)]
pub struct NodeContext<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators> {
    reg_map: R,
    points_to: P,
    subprocedure_locators: S,
}

impl<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators> NodeContextMapping
    for NodeContext<R, P, S>
{
    fn apply_def(&self, term: &Term<Def>) -> Self {
        let r = self.reg_map.apply_def(term);
        let p = self.points_to.apply_def(term);
        let s = self.subprocedure_locators.apply_def(term);
        NodeContext::new(r, p, s)
    }
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
        let memop = Memop {
            sz: v_into.size,
            addr: address.clone(),
            reg_value: typ_var,
            reg_constraints: constraints,
        };
        memop.apply_mem_op(&self.points_to, vman, Self::make_loaded_tvar, true)
    }

    fn make_store_tvar(var: TypeVariableAccess) -> DerivedTypeVar {
        Self::make_mem_tvar(var, FieldLabel::Store)
    }

    fn apply_store(
        &self,
        tid: &Tid,
        value_from: &Expression,
        address_into: &Expression,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        info!("{}: store", tid);
        let (reg_val, constraints) = self.evaluate_expression(value_from, vman);
        info!("{}: store {}", tid, reg_val);

        let memop = Memop {
            sz: value_from.bytesize(),
            addr: address_into.clone(),
            reg_value: reg_val,
            reg_constraints: constraints,
        };
        memop.apply_mem_op(&self.points_to, vman, Self::make_store_tvar, false)
    }

    fn handle_def(&self, df: &Term<Def>, vman: &mut VariableManager) -> ConstraintSet {
        match &df.term {
            Def::Load { var, address } => {
                let cons = self.apply_load(&df.tid, var, address, vman);
                cons
            }
            Def::Store { address, value } => self.apply_store(&df.tid, value, address, vman),
            Def::Assign { var, value } => self.apply_assign(&df.tid, var, value, vman),
        }
    }

    fn argtvar_to_dtv(tvar: ArgTvar, written: bool) -> DerivedTypeVar {
        match tvar {
            ArgTvar::VariableTvar(tv) => DerivedTypeVar::new(tv),
            ArgTvar::MemTvar(tv_access) => {
                if written {
                    Self::make_store_tvar(tv_access)
                } else {
                    Self::make_loaded_tvar(tv_access)
                }
            }
        }
    }

    fn create_formal_tvar<T>(
        indx: usize,
        index_to_field_label: &impl Fn(usize) -> FieldLabel,
        sub: &Term<T>,
    ) -> DerivedTypeVar {
        let mut base = DerivedTypeVar::new(term_to_tvar(&sub));
        base.add_field_label(index_to_field_label(indx));
        base
    }

    fn make_constraints<T>(
        &self,
        sub: &Term<T>,
        args: &[Arg],
        index_to_field_label: &impl Fn(usize) -> FieldLabel,
        arg_is_written: bool,
        vm: &mut VariableManager,
    ) -> ConstraintSet {
        let mut start_constraints = ConstraintSet::default();
        for (i, arg) in args.iter().enumerate() {
            let formal_tv = Self::create_formal_tvar(i, index_to_field_label, sub);
            let (arg_tvars, add_cons) = self
                .subprocedure_locators
                .get_type_variables_and_constraints_for_arg(
                    arg,
                    &self.reg_map,
                    &self.points_to,
                    vm,
                );

            start_constraints.insert_all(&add_cons);

            for arg_repr_tvar in arg_tvars {
                let dt = Self::argtvar_to_dtv(arg_repr_tvar, arg_is_written);
                let new_cons = if arg_is_written {
                    SubtypeConstraint::new(formal_tv.clone(), dt)
                } else {
                    SubtypeConstraint::new(dt, formal_tv.clone())
                };
                start_constraints.insert(new_cons);
            }
        }
        start_constraints
    }

    /// make each formal the subtype of the addressing info for this parameter within the current state
    fn handle_entry_formals(&self, sub: &Term<Sub>, vman: &mut VariableManager) -> ConstraintSet {
        self.make_constraints(
            sub,
            &sub.term.formal_args,
            &|i| FieldLabel::In(i),
            true,
            vman,
        )
    }

    /// make each formal the subtype of the addressing info for this parameter within the current state
    fn handle_retun_formals(&self, sub: &Term<Sub>, vman: &mut VariableManager) -> ConstraintSet {
        self.make_constraints(
            sub,
            &sub.term.formal_rets,
            &|i| FieldLabel::Out(i),
            false,
            vman,
        )
    }

    fn handle_return_actual(&self, sub: &Term<Sub>, vman: &mut VariableManager) -> ConstraintSet {
        self.make_constraints(
            sub,
            &sub.term.formal_rets,
            &|i| FieldLabel::Out(i),
            true,
            vman,
        )
    }

    fn handle_call_actual(&self, sub: &Term<Sub>, vman: &mut VariableManager) -> ConstraintSet {
        self.make_constraints(
            sub,
            &sub.term.formal_args,
            &|i| FieldLabel::In(i),
            false,
            vman,
        )
    }

    fn handle_extern_actual_params(
        &self,
        sub: &Term<ExternSymbol>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        self.make_constraints(
            sub,
            &sub.term.parameters,
            &|i| FieldLabel::In(i),
            false,
            vman,
        )
    }

    fn handle_extern_actual_rets(
        &self,
        sub: &Term<ExternSymbol>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        self.make_constraints(
            sub,
            &sub.term.return_values,
            &|i| FieldLabel::Out(i),
            true,
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
pub struct Context<'a, R, P, S>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    graph: &'a Graph<'a>,
    node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
    extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
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
        extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
    ) -> Context<'a, R, P, S> {
        Context {
            graph,
            node_contexts,
            extern_symbols,
        }
    }

    fn blk_does_return(blk: &Term<Blk>) -> bool {
        blk.term.jmps.iter().any(|jmp| {
            if let Jmp::Return(_) = jmp.term {
                true
            } else {
                false
            }
        })
    }

    fn handle_block_start(
        nd_ctxt: NodeContext<R, P, S>,
        blk: &Term<Blk>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        fold_over_definition_states(
            nd_ctxt,
            blk,
            ConstraintSet::default(),
            &mut |df: &Term<Def>,
                  curr_ctxt: &NodeContext<R, P, S>,
                  mut curr_constraints: ConstraintSet| {
                curr_constraints.insert_all(&curr_ctxt.handle_def(df, vman));
                curr_constraints
            },
        )
    }

    fn collect_extern_call_constraints(
        &self,
        edges: &[Term<Jmp>],
        nd_ctxt: &NodeContext<R, P, S>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
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
            .map(|ext| {
                let cons = nd_ctxt.handle_extern_actual_params(&ext, vman);
                cons
            })
            .fold(ConstraintSet::default(), |mut prev, nxt| {
                prev.insert_all(&nxt);
                prev
            })
    }

    fn edges_to_edge_iter<E, Ty: EdgeType, Idx: IndexType>(
        edges: Edges<E, Ty, Idx>,
    ) -> impl Iterator<Item = &E> {
        edges.map(|x| x.weight())
    }

    fn collect_extern_ret_constraints(
        &self,
        edges: impl Iterator<Item = &'a Edge<'a>>,
        nd_ctxt: &NodeContext<R, P, S>,
        vman: &mut VariableManager,
    ) -> ConstraintSet {
        let mut cons = ConstraintSet::default();
        for edge in edges {
            if let Edge::ExternCallStub(jmp) = edge {
                if let Jmp::Call { target, .. } = &jmp.term {
                    if let Some(extern_symb) = self.extern_symbols.get(target) {
                        let term = Term {
                            term: extern_symb.clone(),
                            tid: target.clone(),
                        };

                        cons.insert_all(&nd_ctxt.handle_extern_actual_rets(&term, vman));
                    }
                }
            }
        }
        cons
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
                Node::BlkStart(blk, sub) => {
                    // TODO(ian): if there is an incoming extern call then we need to add the extern actual rets

                    let mut total_cons = ConstraintSet::default();

                    let incoming_edges = Self::edges_to_edge_iter(
                        self.graph.edges_directed(nd_ind, EdgeDirection::Incoming),
                    );

                    let add_cons =
                        self.collect_extern_ret_constraints(incoming_edges, nd_cont, vman);

                    total_cons.insert_all(&add_cons);

                    if blk.tid == sub.term.blocks[0].tid {
                        let ent_cons = nd_cont.handle_entry_formals(sub, vman);
                        total_cons.insert_all(&ent_cons);
                    }
                    let new_context: NodeContext<R, P, S> = (*nd_cont).clone();
                    total_cons.insert_all(&Self::handle_block_start(new_context, blk, vman));
                    total_cons
                }
                Node::CallReturn {
                    call: (_call_blk, _calling_proc),
                    return_: (_returned_to_blk, return_proc),
                } => nd_cont.handle_return_actual(return_proc, vman),
                Node::CallSource {
                    source: _source,
                    target: (_calling_blk, target_func),
                } => nd_cont.handle_call_actual(target_func, vman),
                // block post conditions arent needed to generate constraints
                Node::BlkEnd(blk, sub) => {
                    let mut cs = ConstraintSet::default();

                    let add_cons =
                        self.collect_extern_call_constraints(&blk.term.jmps, nd_cont, vman);
                    cs.insert_all(&add_cons);

                    // TODO(ian): if there is an outgoing extern call then we need to add the actual args
                    if Self::blk_does_return(blk) {
                        cs.insert_all(&nd_cont.handle_retun_formals(&sub, vman));
                    }

                    cs
                }
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
