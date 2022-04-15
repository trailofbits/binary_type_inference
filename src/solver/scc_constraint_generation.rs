use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    iter::FromIterator,
    marker::PhantomData,
    vec,
};

use alga::general::Lattice;
use cwe_checker_lib::{
    analysis::graph::Graph,
    intermediate_representation::{ExternSymbol, Tid},
};
use petgraph::{dot::Dot, graph::NodeIndex, EdgeDirection::Outgoing};

use super::{
    constraint_graph::{RuleContext, FSA},
    type_lattice::{NamedLattice, NamedLatticeElement},
    type_sketch::{insert_dtv, LatticeBounds, SketchBuilder, SketchGraph},
};
use crate::{
    analysis::callgraph::CallGraph,
    constraint_generation::{
        self, NodeContext, PointsToMapping, RegisterMapping, SubprocedureLocators,
    },
    constraints::{
        AddConstraint, ConstraintSet, DerivedTypeVar, FieldLabel, SubtypeConstraint, TyConstraint,
        TypeVariable, VariableManager,
    },
    pb_constraints::DerivedTypeVariable,
};

// TODO(ian): dont use the tid filter and instead lookup the set of target nodes to traverse or use intraproc graphs. This is ineffecient
pub struct Context<'a, 'b, 'c, R, P, S, T, U>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    cg: CallGraph,
    graph: &'a Graph<'a>,
    node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
    extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
    rule_context: RuleContext,
    vman: &'b mut VariableManager,
    lattice: &'c T,
    type_lattice_elements: HashSet<TypeVariable>,
    weakest_integral_type: U,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct SCCConstraints {
    pub scc: Vec<Tid>,
    pub constraints: ConstraintSet,
}

// There are only two types in the world :)
#[derive(Clone, Copy)]
enum TypeLabels {
    Int,
    Pointer,
}

#[derive(Clone, Copy)]
enum PositionTy {
    LhsTy,
    RhsTy,
    ResTy,
}

#[derive(Clone)]
struct LabelUpdate {
    pub affected_ty: PositionTy,
    pub type_source: Vec<PositionTy>,
    pub new_label: TypeLabels,
}

struct InferenceRules<'a, U: Lattice + Clone> {
    labels: &'a mut HashMap<NodeIndex, TypeLabels>,
    sg: &'a SketchGraph<LatticeBounds<U>>,
}

impl<'a, U> InferenceRules<'a, U>
where
    U: Lattice + Clone,
{
    fn lookup_label(&self, cons: &DerivedTypeVar) -> Option<TypeLabels> {
        self.sg
            .get_graph()
            .get_node(cons)
            .and_then(|idx| self.labels.get(idx).cloned())
    }

    fn add_constraint_to_pattern(
        &self,
        add_cons: &AddConstraint,
    ) -> (Option<TypeLabels>, Option<TypeLabels>, Option<TypeLabels>) {
        (
            self.lookup_label(&add_cons.lhs_ty),
            self.lookup_label(&add_cons.rhs_ty),
            self.lookup_label(&add_cons.repr_ty),
        )
    }

    fn access_by_pos(add_cons: &AddConstraint, pos: PositionTy) -> &DerivedTypeVar {
        match pos {
            PositionTy::LhsTy => &add_cons.lhs_ty,
            PositionTy::RhsTy => &add_cons.rhs_ty,
            PositionTy::ResTy => &add_cons.repr_ty,
        }
    }

    fn cons_to_label_update(&self, add_cons: &AddConstraint) -> Vec<LabelUpdate> {
        match self.add_constraint_to_pattern(add_cons) {
            (Some(TypeLabels::Int), Some(TypeLabels::Int), None) => vec![LabelUpdate {
                affected_ty: PositionTy::ResTy,
                type_source: vec![PositionTy::LhsTy, { PositionTy::RhsTy }],
                new_label: TypeLabels::Int,
            }],
            _ => vec![],
        }
    }

    fn apply_label_update(
        &mut self,
        add_cons: &AddConstraint,
        label_update: &LabelUpdate,
    ) -> Vec<SubtypeConstraint> {
        let tgt_ty = Self::access_by_pos(add_cons, label_update.affected_ty);

        if let Some(tgt_node) = self.sg.get_graph().get_node(tgt_ty) {
            self.labels.insert(*tgt_node, label_update.new_label);
        }

        label_update
            .type_source
            .iter()
            .map(|src| SubtypeConstraint {
                lhs: tgt_ty.clone(),
                rhs: Self::access_by_pos(add_cons, *src).clone(),
            })
            .collect()
    }

    fn apply_add_constraints(&mut self, cons: &[AddConstraint]) -> Vec<SubtypeConstraint> {
        let updates = cons
            .iter()
            .map(|add| (add, self.cons_to_label_update(add)))
            .collect::<Vec<_>>();

        updates
            .iter()
            .map(|(cons, updates)| {
                updates
                    .iter()
                    .map(|update| self.apply_label_update(cons, update))
                    .collect::<Vec<_>>()
            })
            .flatten()
            .flatten()
            .collect()
    }
}

impl<R, P, S, T, U> Context<'_, '_, '_, R, P, S, T, U>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    U: NamedLatticeElement,
    T: NamedLattice<U>,
{
    pub fn new<'a, 'b, 'c>(
        cg: CallGraph,
        graph: &'a Graph<'a>,
        node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
        extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
        rule_context: RuleContext,
        vman: &'b mut VariableManager,
        lattice: &'c T,
        type_lattice_elements: HashSet<TypeVariable>,
        weakest_integral_type: U,
    ) -> Context<'a, 'b, 'c, R, P, S, T, U> {
        Context {
            cg,
            graph,
            node_contexts,
            extern_symbols,
            rule_context,
            vman,
            lattice,
            type_lattice_elements,
            weakest_integral_type,
        }
    }

    fn get_initial_labeling(
        &self,
        sg: &SketchGraph<LatticeBounds<U>>,
    ) -> HashMap<NodeIndex, TypeLabels> {
        let pointers = sg
            .get_graph()
            .get_graph()
            .node_indices()
            .filter(|idx| {
                sg.get_graph()
                    .get_graph()
                    .edges_directed(*idx, Outgoing)
                    .any(|e| {
                        matches!(e.weight(), FieldLabel::Load)
                            || matches!(e.weight(), FieldLabel::Store)
                    })
            })
            .collect::<BTreeSet<_>>();

        let integers = sg
            .get_graph()
            .get_graph()
            .node_indices()
            .filter(|idx| {
                let nd = &sg.get_graph().get_graph()[*idx];
                nd.get_upper() <= &self.weakest_integral_type && !pointers.contains(idx)
            })
            .map(|idx| (idx, TypeLabels::Int));

        integers
            .chain(pointers.iter().map(|idx| (*idx, TypeLabels::Pointer)))
            .collect()
    }

    /// Constructs a new constraint set that infers wether an argument of an addition constraint is a pointer or an integer based on some inference rules.
    fn infer_pointers(&self, orig_cs_set: &ConstraintSet) -> anyhow::Result<ConstraintSet> {
        let mut next_cs_set = orig_cs_set.clone();

        let add_constraints = next_cs_set
            .iter()
            .filter_map(|x| {
                if let TyConstraint::AddCons(acons) = x {
                    Some(acons.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        while {
            let mut curr_set = next_cs_set.clone();
            let sg =
                SketchBuilder::new(self.lattice, &self.type_lattice_elements, &|dtv, mpgrph| {
                    insert_dtv(self.lattice, mpgrph, dtv.clone());
                    Ok(())
                })
                .build_and_label_constraints(&next_cs_set)?;
            let mut base_labels = self.get_initial_labeling(&sg);

            let mut irules = InferenceRules {
                labels: &mut base_labels,
                sg: &sg,
            };

            for cons in irules.apply_add_constraints(&add_constraints) {
                curr_set.insert(TyConstraint::SubTy(cons));
            }

            let changed = curr_set != next_cs_set;
            next_cs_set = curr_set;
            changed
        } {}

        Ok(next_cs_set)
    }

    pub fn get_simplified_constraints(&mut self) -> anyhow::Result<Vec<SCCConstraints>> {
        let maybe_scc: anyhow::Result<Vec<SCCConstraints>> = petgraph::algo::tarjan_scc(&self.cg)
            .into_iter()
            .map(|scc| {
                let tid_filter: HashSet<Tid> = scc
                    .into_iter()
                    .map(|nd| self.cg.node_weight(nd).unwrap())
                    .cloned()
                    .collect();
                let cont = constraint_generation::Context::new(
                    self.graph,
                    &self.node_contexts,
                    self.extern_symbols,
                    Some(tid_filter.clone()),
                );

                let basic_cons = cont.generate_constraints(self.vman);
                println!("Cons for: {:#?}", tid_filter);
                println!("Basic cons: {}", basic_cons);

                let mut fsa = FSA::new(&basic_cons, &self.rule_context)?;

                fsa.simplify_graph(self.vman);

                let cons = fsa.walk_constraints();

                Ok(SCCConstraints {
                    scc: Vec::from_iter(tid_filter.into_iter()),
                    constraints: cons,
                })
            })
            .collect();

        maybe_scc
    }
}
