use std::collections::{BTreeSet, HashSet};
use std::marker::PhantomData;
use std::{collections::HashMap, hash::Hash};

use alga::general::{AbstractMagma, Lattice};
use itertools::Itertools;
use log::info;
use petgraph::dot::Dot;
use petgraph::graph::DefaultIx;
use petgraph::unionfind::UnionFind;
use petgraph::visit::{Dfs, EdgeRef, IntoEdgeReferences, IntoNodeReferences};
use petgraph::visit::{IntoEdgesDirected, Walker};
use petgraph::{
    data::Build,
    graph::NodeIndex,
    graph::{EdgeIndex, Graph},
    Directed,
};

use crate::constraints::{
    ConstraintSet, DerivedTypeVar, FieldLabel, TyConstraint, TypeVariable, Variance,
};

use super::constraint_graph::RuleContext;
use super::type_lattice::{NamedLattice, NamedLatticeElement};
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
            let _new_node = nd.add_node(grp.clone());
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
    pub fn get_graph(&self) -> &NodeDefinedGraph<DerivedTypeVar, FieldLabel> {
        &self.grph
    }

    pub fn get_quotient_graph(&self) -> &NodeDefinedGraph<BTreeSet<NodeIndex>, FieldLabel> {
        &self.quotient_graph
    }

    fn insert_dtv(grph: &mut NodeDefinedGraph<DerivedTypeVar, FieldLabel>, dtv: DerivedTypeVar) {
        let mut curr_var = DerivedTypeVar::new(dtv.get_base_variable().clone());

        let mut prev = grph.add_node(curr_var.clone());
        for fl in dtv.get_field_labels() {
            curr_var.add_field_label(fl.clone());
            let next = grph.add_node(curr_var.clone());
            grph.add_edge(prev, next, fl.clone());
            prev = next;
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

        for (nd_idx, grouplab) in cons.clone().into_labeling().into_iter().enumerate() {
            let nd_idx: NodeIndex = NodeIndex::new(nd_idx);
            let nd = grph.get_graph().node_weight(nd_idx).unwrap();
            info!("Node {}: {} in group {}", nd_idx.index(), nd, grouplab);
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

            Some((*node_map.get(&root).unwrap(), reachable_subgraph))
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

pub struct LabelingContext<U: NamedLatticeElement, T: NamedLattice<U>> {
    lattice: T,
    nm: std::marker::PhantomData<U>,
    type_lattice_elements: HashSet<TypeVariable>,
}

impl<U: NamedLatticeElement, T: NamedLattice<U>> LabelingContext<U, T> {
    pub fn new(lattice: T, elements: HashSet<TypeVariable>) -> Self {
        Self {
            lattice,
            type_lattice_elements: elements,
            nm: PhantomData,
        }
    }

    fn construct_variance(
        &self,
        entry: NodeIndex,
        orig_graph: &Graph<(), FieldLabel>,
    ) -> Graph<U, FieldLabel> {
        // Stores who we visited and how we visited them.
        let mut visited: HashMap<NodeIndex, Vec<FieldLabel>> = HashMap::new();

        let mut to_visit = Vec::new();
        to_visit.push((entry, Vec::new()));

        while let Some((next_nd, path)) = to_visit.pop() {
            if visited.contains_key(&next_nd) {
                continue;
            }

            visited.insert(next_nd, path.clone());

            for e in orig_graph.edges_directed(next_nd, petgraph::EdgeDirection::Outgoing) {
                if !visited.contains_key(&e.target()) {
                    let mut next_path = path.clone();
                    next_path.push(e.weight().clone());
                    to_visit.push((e.target(), next_path));
                }
            }
        }

        let variances: HashMap<_, _> = visited
            .into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.iter()
                        .map(|x| x.variance())
                        .reduce(|x, y| x.operate(&y))
                        .unwrap_or(Variance::Covariant),
                )
            })
            .collect();
        orig_graph.map(
            |nd_idx, _| match variances.get(&nd_idx).unwrap() {
                Variance::Covariant => self.lattice.top(),
                Variance::Contravariant => self.lattice.bot(),
            },
            |_, e| e.clone(),
        )
    }

    fn get_initial_labels(
        &self,
        initial_sketches: HashMap<TypeVariable, (NodeIndex, Graph<(), FieldLabel>)>,
    ) -> HashMap<TypeVariable, (NodeIndex, Graph<U, FieldLabel>)> {
        let unlabeled = initial_sketches
            .into_iter()
            .map(|(k, (entry, graph))| (k, (entry, self.construct_variance(entry, &graph))));
        unlabeled.collect()
    }

    fn dtv_is_uninterpreted_lattice(&self, dtv: &DerivedTypeVar) -> bool {
        self.type_lattice_elements.contains(dtv.get_base_variable())
            && dtv.get_field_labels().is_empty()
    }

    // TODO(ian): What about multiple edges with the same weight (paper claims it is prefix closed, is that actually true? can we prove it?)
    fn find_node_following_path<S>(
        entry: NodeIndex,
        path: &[FieldLabel],
        grph: &Graph<S, FieldLabel>,
    ) -> Option<NodeIndex> {
        let mut curr_node = entry;
        for pth_member in path.iter() {
            let found = grph
                .edges_directed(curr_node, petgraph::EdgeDirection::Outgoing)
                .find(|e| e.weight() == pth_member);

            if let Some(found_edge) = found {
                curr_node = found_edge.target();
            } else {
                return None;
            }
        }

        Some(curr_node)
    }

    fn update_lattice_node(
        initial_sketches: &mut HashMap<TypeVariable, (NodeIndex, Graph<U, FieldLabel>)>,
        lattice_elem: U,
        target_dtv: &DerivedTypeVar,
        operation: impl Fn(&U, &U) -> U,
    ) {
        let (entry, grph) = initial_sketches
            .get_mut(target_dtv.get_base_variable())
            .unwrap();

        let target_node_idx =
            Self::find_node_following_path(*entry, target_dtv.get_field_labels(), grph)
                .expect("The sketch for a type variable should acccept its field labels");

        let weight_ref = grph.node_weight_mut(target_node_idx).unwrap();
        *weight_ref = operation(weight_ref, &lattice_elem);
    }

    pub fn label_sketches(
        &self,
        cons: &ConstraintSet,
        init_graph: HashMap<TypeVariable, (NodeIndex, Graph<(), FieldLabel>)>,
    ) -> HashMap<TypeVariable, (NodeIndex, Graph<U, FieldLabel>)> {
        let init = self.get_initial_labels(init_graph);
        self.label_inited_sketches(cons, init)
    }

    fn label_inited_sketches(
        &self,
        cons: &ConstraintSet,
        mut initial_sketches: HashMap<TypeVariable, (NodeIndex, Graph<U, FieldLabel>)>,
    ) -> HashMap<TypeVariable, (NodeIndex, Graph<U, FieldLabel>)> {
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
                    && initial_sketches.contains_key(subty.rhs.get_base_variable())
                {
                    Self::update_lattice_node(
                        &mut initial_sketches,
                        self.lattice
                            .get_elem(subty.lhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.rhs,
                        |x: &U, y: &U| x.join(&y),
                    );
                } else if self.dtv_is_uninterpreted_lattice(&subty.rhs)
                    && initial_sketches.contains_key(subty.lhs.get_base_variable())
                {
                    Self::update_lattice_node(
                        &mut initial_sketches,
                        self.lattice
                            .get_elem(subty.rhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.lhs,
                        |x: &U, y: &U| x.join(&y),
                    );
                }
            });

        initial_sketches
    }
}
