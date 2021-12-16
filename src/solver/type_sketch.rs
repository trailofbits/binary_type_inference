use std::collections::{BTreeSet, HashSet};
use std::{collections::HashMap, hash::Hash};

use itertools::Itertools;
use petgraph::graph::DefaultIx;
use petgraph::unionfind::UnionFind;
use petgraph::visit::Walker;
use petgraph::visit::{Dfs, EdgeRef, IntoEdgeReferences, IntoNodeReferences};
use petgraph::{
    data::Build,
    graph::NodeIndex,
    graph::{EdgeIndex, Graph},
    Directed,
};

use crate::constraints::{ConstraintSet, DerivedTypeVar, FieldLabel, TyConstraint, TypeVariable};

use super::constraint_graph::RuleContext;
// TODO(ian): use this abstraction for the transducer
struct NodeDefinedGraph<N: Clone + Hash + Eq, E: Hash + Eq> {
    grph: Graph<N, E>,
    nodes: HashMap<N, NodeIndex>,
}

impl<N: Clone + Hash + Eq, E: Hash + Eq + Clone> NodeDefinedGraph<N, E> {
    pub fn new() -> NodeDefinedGraph<N, E> {
        NodeDefinedGraph {
            grph: Graph::new(),
            nodes: HashMap::new(),
        }
    }

    pub fn get_graph(&self) -> &Graph<N, E> {
        &self.grph
    }

    pub fn edges_between(
        &self,
        a: NodeIndex,
        b: NodeIndex,
    ) -> impl Iterator<Item = EdgeIndex> + '_ {
        self.grph
            .edges_directed(a, petgraph::EdgeDirection::Outgoing)
            .filter(move |x| x.target() == b)
            .map(|x| x.id())
    }

    pub fn add_edge(&mut self, a: NodeIndex, b: NodeIndex, e: E) -> bool {
        if !self
            .edges_between(a, b)
            .any(|x| self.grph.edge_weight(x) == Some(&e))
        {
            self.grph.add_edge(a, b, e);
            true
        } else {
            false
        }
    }

    pub fn get_node(&self, wt: &N) -> Option<&NodeIndex> {
        self.nodes.get(wt)
    }

    pub fn add_node(&mut self, wt: N) -> NodeIndex {
        if let Some(x) = self.nodes.get(&wt) {
            *x
        } else {
            let nd = self.grph.add_node(wt.clone());
            self.nodes.insert(wt, nd);
            nd
        }
    }

    pub fn quoetient_graph(
        &self,
        groups: &Vec<BTreeSet<NodeIndex>>,
    ) -> NodeDefinedGraph<BTreeSet<NodeIndex>, E> {
        let mut nd: NodeDefinedGraph<BTreeSet<NodeIndex>, E> = NodeDefinedGraph::new();

        let repr_mapping = groups
            .iter()
            .enumerate()
            .map(|(repr_indx, s)| s.iter().map(move |node_idx| (node_idx, repr_indx)))
            .flatten()
            .collect::<HashMap<_, _>>();

        for grp in groups.iter() {
            let new_node = nd.add_node(grp.clone());
        }

        for edge in self.get_graph().edge_references() {
            let repr_src = &groups[*repr_mapping.get(&edge.source()).unwrap()];
            let repr_dst = &groups[*repr_mapping.get(&edge.target()).unwrap()];

            let src_node = nd.add_node(repr_src.clone());
            let dst_node = nd.add_node(repr_dst.clone());
            nd.add_edge(src_node, dst_node, edge.weight().clone());
        }

        nd
    }
}

// TODO(ian): these graphs are awfully similar is there some refactoring that can be done
struct SketchGraph {
    grph: NodeDefinedGraph<DerivedTypeVar, FieldLabel>,
    quotient_graph: NodeDefinedGraph<BTreeSet<NodeIndex>, FieldLabel>,
    constraint_to_group: HashMap<NodeIndex, NodeIndex>,
}

// an equivalence between eq nodes implies an equivalence between edge
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
struct EdgeImplication {
    eq: (NodeIndex, NodeIndex),
    edge: (NodeIndex, NodeIndex),
}

impl SketchGraph {
    fn insert_dtv(grph: &mut NodeDefinedGraph<DerivedTypeVar, FieldLabel>, dtv: DerivedTypeVar) {
        let mut curr_var = DerivedTypeVar::new(dtv.get_base_variable().clone());

        let mut prev = grph.add_node(curr_var.clone());
        for fl in dtv.get_field_labels() {
            curr_var.add_field_label(fl.clone());
            let next = grph.add_node(curr_var.clone());
            grph.add_edge(prev, next, fl.clone());
        }
    }

    fn dts_from_constraint_set(s: &ConstraintSet) -> impl Iterator<Item = &DerivedTypeVar> {
        s.iter()
            .filter_map(|x| {
                if let TyConstraint::SubTy(x) = x {
                    Some(vec![&x.lhs, &x.rhs].into_iter())
                } else {
                    None
                }
            })
            .flatten()
    }

    fn constraint_quotients(
        grph: &NodeDefinedGraph<DerivedTypeVar, FieldLabel>,
        cons: &ConstraintSet,
    ) -> UnionFind<usize> {
        if cons.is_empty() {
            return UnionFind::new(0);
        }

        let num_vars = grph;
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
        grph: &NodeDefinedGraph<DerivedTypeVar, FieldLabel>,
    ) -> HashSet<EdgeImplication> {
        grph.get_graph()
            .edge_indices()
            .cartesian_product(grph.get_graph().edge_indices())
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

    fn quoetient_graph(
        grph: &NodeDefinedGraph<DerivedTypeVar, FieldLabel>,
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

        cons.into_labeling()
            .into_iter()
            .enumerate()
            .map(|(ndidx, repr)| (NodeIndex::new(ndidx), repr))
            .group_by(|(_, repr)| *repr)
            .into_iter()
            .map(|(_, grp)| grp.map(|(idx, _)| idx).collect::<BTreeSet<_>>())
            .collect()
    }

    pub fn new(s: &ConstraintSet) -> SketchGraph {
        let mut nd = NodeDefinedGraph::new();

        Self::dts_from_constraint_set(s)
            .cloned()
            .for_each(|f| Self::insert_dtv(&mut nd, f));

        let labeled = Self::quoetient_graph(&nd, s);
        let quotient_graph = nd.quoetient_graph(&labeled);

        let old_to_new = quotient_graph
            .get_graph()
            .node_references()
            .map(|(idx, child_node)| child_node.iter().map(move |child| (*child, idx)))
            .flatten()
            .collect();

        SketchGraph {
            grph: nd,
            quotient_graph,
            constraint_to_group: old_to_new,
        }
    }

    fn get_repr_idx(&self, dt: &DerivedTypeVar) -> Option<NodeIndex> {
        self.grph
            .get_node(&dt)
            .and_then(|old_idx| self.constraint_to_group.get(old_idx))
            .cloned()
    }

    fn add_edges_to_subgraph(
        &self,
        start: NodeIndex,
        node_map: &HashMap<NodeIndex, NodeIndex>,
        subgraph: &mut Graph<(), FieldLabel>,
    ) {
        for e in self
            .quotient_graph
            .get_graph()
            .edges_directed(start, petgraph::EdgeDirection::Outgoing)
        {
            subgraph.add_edge(
                *node_map.get(&e.source()).unwrap(),
                *node_map.get(&e.target()).unwrap(),
                e.weight().clone(),
            );
        }
    }
    /// retrieves a graph for the given DerivedTypeVariable where it is the root and it contains all remaining paths these maps can serve as the basis for sketches
    pub fn get_repr_graph(
        &self,
        dt: &DerivedTypeVar,
    ) -> Option<(NodeIndex, Graph<(), FieldLabel>)> {
        let root = self.get_repr_idx(dt);

        if let Some(root) = root {
            let dfs = Dfs::new(self.quotient_graph.get_graph(), root);
            let mut reachable_subgraph = Graph::new();
            let reachable: Vec<_> = dfs.iter(self.quotient_graph.get_graph()).collect();
            let node_map = reachable
                .iter()
                .map(|old| {
                    let new = reachable_subgraph.add_node(());
                    (*old, new)
                })
                .collect::<HashMap<_, _>>();
            reachable
                .iter()
                .for_each(|x| self.add_edges_to_subgraph(*x, &node_map, &mut reachable_subgraph));

            Some((root, reachable_subgraph))
        } else {
            None
        }
    }
}

/// Gets initial unlabeled sketches
pub fn get_initial_sketches(
    cons: &ConstraintSet,
    rule_context: &RuleContext,
) -> HashMap<TypeVariable, (NodeIndex, Graph<(), FieldLabel>)> {
    let initial_sketch_builder = SketchGraph::new(cons);

    rule_context
        .get_interesting()
        .iter()
        .filter_map(|x| {
            initial_sketch_builder
                .get_repr_graph(&DerivedTypeVar::new(x.clone()))
                .map(|scheme_def| (x.clone(), scheme_def))
        })
        .collect()
}
