use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::marker::PhantomData;
use std::rc::Rc;
use std::{collections::HashMap, hash::Hash};

use alga::general::{
    AbstractMagma, Additive, AdditiveMagma, Identity, JoinSemilattice, Lattice, MeetSemilattice,
};
use anyhow::Context;
use cwe_checker_lib::analysis::graph;
use cwe_checker_lib::intermediate_representation::Tid;
use env_logger::Target;
use itertools::Itertools;
use log::info;
use petgraph::graph::IndexType;
use petgraph::stable_graph::{StableDiGraph, StableGraph};
use petgraph::unionfind::UnionFind;
use petgraph::visit::{Dfs, EdgeRef, IntoEdgeReferences, IntoEdgesDirected, IntoNodeReferences};
use petgraph::visit::{IntoNodeIdentifiers, Walker};
use petgraph::{algo, EdgeType};
use petgraph::{
    graph::NodeIndex,
    graph::{EdgeIndex, Graph},
};

use crate::analysis::callgraph::CallGraph;
use crate::constraint_generation;
use crate::constraints::{
    ConstraintSet, DerivedTypeVar, FieldLabel, TyConstraint, TypeVariable, Variance,
};
use crate::graph_algos::mapping_graph::{self, MappingGraph};

use super::constraint_graph::TypeVarNode;
use super::type_lattice::{CustomLatticeElement, NamedLattice, NamedLatticeElement};

// an equivalence between eq nodes implies an equivalence between edge
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
struct EdgeImplication {
    eq: (NodeIndex, NodeIndex),
    edge: (NodeIndex, NodeIndex),
}

/// Labels for the sketch graph that mantain both an upper bound and lower bound on merged type
#[derive(Clone, PartialEq)]
pub struct LatticeBounds<T: Clone + Lattice> {
    upper_bound: T,
    lower_bound: T,
}

impl<T> LatticeBounds<T>
where
    T: Lattice,
    T: Clone,
{
    fn join(&self, other: &T) -> Self {
        Self {
            upper_bound: self.upper_bound.clone(),
            lower_bound: self.lower_bound.join(other),
        }
    }

    fn meet(&self, other: &T) -> Self {
        Self {
            upper_bound: self.upper_bound.meet(other),
            lower_bound: self.lower_bound.clone(),
        }
    }
}

// TODO(ian): This is probably an abelian group, but that requires an identity implementation which is hard because that requires a function that can produce a
// top and bottom element without context but top and bottom are runtime defined.
impl<T> AbstractMagma<Additive> for LatticeBounds<T>
where
    T: Lattice,
    T: Clone,
{
    fn operate(&self, right: &Self) -> Self {
        LatticeBounds {
            upper_bound: right.upper_bound.meet(&self.upper_bound),
            lower_bound: right.lower_bound.join(&self.lower_bound),
        }
    }
}

/// Creates a structured and labeled sketch graph
/// This algorithm creates polymorphic function types.
/// Type information flows up to callers but not down to callees (callees wont be unified).
/// The reachable subgraph of the callee is copied up to the caller. Callee nodes are labeled.
struct SketckGraphBuilder<'a, U: NamedLatticeElement, T: NamedLattice<U>> {
    // Allows us to map any tid to the correct constraintset
    scc_signatures: HashMap<Tid, Rc<ConstraintSet>>,
    // Collects a shared sketchgraph representing the functions in the SCC
    scc_repr: HashMap<TypeVariable, Rc<SketchGraph<LatticeBounds<U>>>>,
    cg: CallGraph,
    lattice: &'a T,
    type_lattice_elements: HashSet<TypeVariable>,
}

impl<'a, U: NamedLatticeElement, T: NamedLattice<U>> SketckGraphBuilder<'a, U, T>
where
    T: 'a,
{
    /// The identity operation described for Lattice bounds
    fn identity_element(&self) -> LatticeBounds<U> {
        let bot = self.lattice.bot();
        let top = self.lattice.top();
        LatticeBounds {
            upper_bound: top,
            lower_bound: bot,
        }
    }

    fn insert_dtv(
        &self,
        grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        dtv: DerivedTypeVar,
    ) {
        let mut curr_var = DerivedTypeVar::new(dtv.get_base_variable().clone());

        let mut prev = grph.add_node(curr_var.clone(), self.identity_element());
        for fl in dtv.get_field_labels() {
            curr_var.add_field_label(fl.clone());
            let next = grph.add_node(curr_var.clone(), self.identity_element());
            grph.add_edge(prev, next, fl.clone());
            prev = next;
        }
    }

    fn add_variable(
        &self,
        var: &DerivedTypeVar,
        is_internal_variable: &BTreeSet<TypeVariable>,
        nd_graph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
    ) -> anyhow::Result<()> {
        if is_internal_variable.contains(var.get_base_variable()) {
            self.insert_dtv(&mut nd_graph, var.clone());
        } else {
            let ext = self
                .scc_repr
                .get(var.get_base_variable())
                .ok_or(anyhow::anyhow!(
                    "An external variable must have a representation already built"
                ))?;

            ext.copy_reachable_subgraph_into(var, nd_graph);
        }

        Ok(())
    }

    fn add_nodes_and_initial_edges(
        &self,
        representing: &Vec<Tid>,
        cs_set: &ConstraintSet,
        nd_graph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
    ) -> anyhow::Result<()> {
        let is_internal_variable = representing
            .iter()
            .map(|x| constraint_generation::tid_to_tvar(x))
            .collect::<BTreeSet<_>>();

        for constraint in cs_set.iter() {
            if let TyConstraint::SubTy(sty) = constraint {
                self.add_variable(&sty.lhs, &is_internal_variable, nd_graph);
                self.add_variable(&sty.rhs, &is_internal_variable, nd_graph);
            }
        }

        Ok(())
    }

    fn dtv_is_uninterpreted_lattice(&self, dtv: &DerivedTypeVar) -> bool {
        self.type_lattice_elements.contains(dtv.get_base_variable())
            && dtv.get_field_labels().is_empty()
    }

    fn update_lattice_node(
        grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        lattice_elem: U,
        target_dtv: &DerivedTypeVar,
        operation: impl Fn(&U, &LatticeBounds<U>) -> LatticeBounds<U>,
    ) {
        let target_group_idx = *grph.get_node(target_dtv).unwrap();
        let orig_value = grph
            .get_graph_mut()
            .node_weight_mut(target_group_idx)
            .unwrap();
        *orig_value = operation(&lattice_elem, orig_value);
    }

    fn label_by(
        &self,
        grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        cons: &ConstraintSet,
    ) {
        cons.iter()
            .filter_map(|x| {
                if let TyConstraint::SubTy(sy) = x {
                    Some(sy)
                } else {
                    None
                }
            })
            .for_each(|subty| {
                if self.dtv_is_uninterpreted_lattice(&subty.lhs)
                    && grph.get_node(&subty.rhs).is_some()
                {
                    Self::update_lattice_node(
                        grph,
                        self.lattice
                            .get_elem(subty.lhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.rhs,
                        |x: &U, y: &LatticeBounds<U>| y.join(x),
                    );
                } else if self.dtv_is_uninterpreted_lattice(&subty.rhs)
                    && grph.get_node(&subty.lhs).is_some()
                {
                    Self::update_lattice_node(
                        grph,
                        self.lattice
                            .get_elem(subty.rhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.lhs,
                        |x: &U, y: &LatticeBounds<U>| y.meet(x),
                    );
                }
            });
    }

    fn build_and_label_scc_sketch(&mut self, to_reprs: Vec<Tid>) {
        let sig = self
            .scc_signatures
            .get(&to_reprs[0])
            .expect("scc should have a sig");

        let nd_graph: MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel> =
            MappingGraph::new();

        self.add_nodes_and_initial_edges(&to_reprs, sig, &mut nd_graph);
        let qgroups = Self::generate_quotient_groups(&nd_graph, sig);
        nd_graph.quoetient_graph(&qgroups);

        self.label_by(&mut nd_graph, sig);

        let orig_sk_graph = SketchGraph::from(nd_graph);

        let sk_graph = Rc::new(orig_sk_graph);

        for repr in to_reprs.iter() {
            self.scc_repr
                .insert(constraint_generation::tid_to_tvar(repr), sk_graph.clone());
        }
    }

    fn constraint_quotients(
        grph: &MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        cons: &ConstraintSet,
    ) -> UnionFind<usize> {
        if cons.is_empty() {
            return UnionFind::new(0);
        }

        let mut uf: UnionFind<usize> =
            UnionFind::new(grph.get_graph().node_indices().max().unwrap().index() + 1);

        for cons in cons.iter() {
            if let TyConstraint::SubTy(sub_cons) = cons {
                let lt_node = grph.get_node(&sub_cons.lhs).unwrap();
                let gt_node = grph.get_node(&sub_cons.rhs).unwrap();

                uf.union(lt_node.index(), gt_node.index());
            }
        }

        uf
    }

    fn get_edge_set(
        grph: &MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
    ) -> HashSet<EdgeImplication> {
        grph.get_graph()
            .edge_indices()
            .cartesian_product(grph.get_graph().edge_indices().collect::<Vec<_>>())
            .filter_map(|(e1, e2)| {
                let w1 = grph.get_graph().edge_weight(e1).unwrap();
                let w2 = grph.get_graph().edge_weight(e2).unwrap();
                let (src1, dst1) = grph.get_graph().edge_endpoints(e1).unwrap();
                let (src2, dst2) = grph.get_graph().edge_endpoints(e2).unwrap();

                if w1 == w2 || w1 == &FieldLabel::Load && w2 == &FieldLabel::Store {
                    Some(EdgeImplication {
                        eq: (src1, src2),
                        edge: (dst1, dst2),
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    fn generate_quotient_groups(
        grph: &MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        cons: &ConstraintSet,
    ) -> Vec<BTreeSet<NodeIndex>> {
        let mut cons = Self::constraint_quotients(grph, cons);
        let mut edge_implications = Self::get_edge_set(grph);

        while {
            let prev_labeling = cons.clone().into_labeling();

            for implic in edge_implications.clone().into_iter() {
                if cons.equiv(implic.eq.0.index(), implic.eq.1.index()) {
                    edge_implications.remove(&implic);
                    cons.union(implic.edge.0.index(), implic.edge.1.index());
                }
            }

            cons.clone().into_labeling() != prev_labeling
        } {}

        for (nd_idx, grouplab) in cons.clone().into_labeling().into_iter().enumerate() {
            let nd_idx: NodeIndex = NodeIndex::new(nd_idx);
            let nd = grph.get_graph().node_weight(nd_idx).unwrap();
            info!("Node {}: in group {}", nd_idx.index(), grouplab);
        }

        cons.into_labeling()
            .into_iter()
            .enumerate()
            .map(|(ndidx, repr)| (NodeIndex::new(ndidx), repr))
            .fold(
                HashMap::<usize, BTreeSet<NodeIndex>>::new(),
                |mut total, (nd_ind, repr_group)| {
                    total.entry(repr_group).or_default().insert(nd_ind);
                    total
                },
            )
            .into_values()
            .collect()
    }

    pub fn build(self) -> anyhow::Result<HashMap<TypeVariable, Rc<SketchGraph<LatticeBounds<U>>>>> {
        let condensed = petgraph::algo::condensation(self.cg, false);
        let mut sorted: Vec<NodeIndex> = petgraph::algo::toposort(&condensed, None)
            .map_err(|_| anyhow::anyhow!("cycle error"))
            .with_context(|| {
                "Constructing topological sort of codensed sccs for sketch building"
            })?;

        sorted.reverse();

        for idx in sorted {
            let associated_tids = condensed[idx];
            // condensation shouldnt produce a node that doesnt represent any of the original nodes
            assert!(!associated_tids.is_empty());

            self.build_and_label_scc_sketch(associated_tids);
        }

        Ok(self.scc_repr)
    }
}

/// A constraint graph quotiented over a symmetric subtyping relation.
pub struct SketchGraph<T> {
    quotient_graph: StableGraph<T, FieldLabel>,
    dtv_to_group: HashMap<DerivedTypeVar, NodeIndex>,
    group_to_dtvs: HashMap<NodeIndex, BTreeSet<DerivedTypeVar>>,
}

impl<U: Clone + Lattice> From<MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>>
    for SketchGraph<LatticeBounds<U>>
{
    fn from(input: MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>) -> Self {
        let g = input.get_graph().clone();
        let mapping = input.get_node_mapping().clone();
        let mut rev_mapping = HashMap::new();

        for (k, v) in mapping.iter() {
            let s = rev_mapping.entry(*v).or_insert_with(|| BTreeSet::new());
            s.insert(k.clone());
        }

        SketchGraph {
            quotient_graph: g,
            dtv_to_group: mapping,
            group_to_dtvs: rev_mapping,
        }
    }
}

impl<T: AbstractMagma<Additive> + std::cmp::PartialEq> SketchGraph<T> {
    fn add_idx_to(
        &self,
        reached_idx: NodeIndex,
        into: &mut MappingGraph<T, DerivedTypeVar, FieldLabel>,
    ) {
        let grp = self
            .group_to_dtvs
            .get(&reached_idx)
            .expect("every node should have a group");

        let rand_fst = grp.iter().next().expect("groups should be non empty");
        let _index_in_new_graph = into.add_node(
            rand_fst.clone(),
            self.quotient_graph
                .node_weight(reached_idx)
                .expect("index should have weight")
                .clone(),
        );

        for member in grp.iter() {
            into.merge_nodes(rand_fst.clone(), member.clone());
        }
    }

    fn get_key_and_weight_for_index(&self, idx: NodeIndex) -> (DerivedTypeVar, T) {
        let dtv = self
            .group_to_dtvs
            .get(&idx)
            .expect("every node should have a gorup")
            .iter()
            .next()
            .expect("groups should be non empty");

        (
            dtv.clone(),
            self.quotient_graph
                .node_weight(idx)
                .expect("every node should have a weight")
                .clone(),
        )
    }

    pub fn copy_reachable_subgraph_into(
        &self,
        from: &DerivedTypeVar,
        into: &mut MappingGraph<T, DerivedTypeVar, FieldLabel>,
    ) {
        if let Some(represented) = self.dtv_to_group.get(from) {
            let reachable_idxs: BTreeSet<_> = Dfs::new(&self.quotient_graph, *represented)
                .iter(&self.quotient_graph)
                .collect();

            reachable_idxs
                .iter()
                .for_each(|reached_idx| self.add_idx_to(*reached_idx, into));

            // add edges where both ends are in the subgraph
            for edge in self.quotient_graph.edge_references() {
                if reachable_idxs.contains(&edge.target())
                    && reachable_idxs.contains(&edge.source())
                {
                    let (key1, w1) = self.get_key_and_weight_for_index(edge.source());
                    let source = into.add_node(key1, w1);

                    let (key2, w2) = self.get_key_and_weight_for_index(edge.target());
                    let target = into.add_node(key2, w2);

                    into.add_edge(source, target, edge.weight().clone());
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use petgraph::dot::Dot;

    use crate::constraints::parse_constraint_set;

    use super::SketchGraph;

    #[test]
    fn test_simple_equivalence() {
        // should reduce to one type
        let (rem, test_set) = parse_constraint_set(
            "
            loop_breaker517.load.σ64@40 <= loop_breaker517
            sub_001014fb.out.load.σ64@40 <= loop_breaker517.store.σ64@0
            sub_001014fb.out.load.σ64@40 <= loop_breaker517
            sub_00101728.in_0 <= sub_001014fb.in_0
        ",
        )
        .expect("Should parse constraints");
        assert!(rem.len() == 0);

        //let _grph = SketchGraph::<()>::new(&test_set);
    }

    #[test]
    fn test_double_pointer() {
        // should reduce to one type
        let (rem, test_set) = parse_constraint_set(
            "
            curr_target.load.σ64@0.+8 <= curr_target
            target.load.σ64@8 <= curr_target.store.σ64@0
        ",
        )
        .expect("Should parse constraints");
        assert!(rem.len() == 0);
        /*
        let grph = SketchGraph::<()>::new(&test_set);

        println!(
            "{}",
            Dot::new(
                &grph
                    .quotient_graph
                    .map(|nd_id, _nd_weight| nd_id.index().to_string(), |_e, e2| e2)
            )
        );

        for (dtv, idx) in grph.dtv_to_group.iter() {
            println!("Dtv: {} Group: {}", dtv, idx.index());
        }*/
    }
}
