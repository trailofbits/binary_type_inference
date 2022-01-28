use std::collections::{BTreeSet, HashSet};
use std::marker::PhantomData;
use std::rc::Rc;
use std::{collections::HashMap, hash::Hash};

use alga::general::AbstractMagma;
use itertools::Itertools;
use log::info;
use petgraph::graph::IndexType;
use petgraph::unionfind::UnionFind;
use petgraph::visit::{Dfs, EdgeRef, IntoNodeReferences};
use petgraph::visit::{IntoNodeIdentifiers, Walker};
use petgraph::{algo, EdgeType};
use petgraph::{
    graph::NodeIndex,
    graph::{EdgeIndex, Graph},
};

use crate::constraints::{
    ConstraintSet, DerivedTypeVar, FieldLabel, TyConstraint, TypeVariable, Variance,
};

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
        groups: &[BTreeSet<NodeIndex>],
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

#[derive(Debug, Clone)]
/// A sketch is a graph with edges weighted by field labels.
/// These sketches represent the type of the type variable.
/// The sketch stores the entry index to the graph for convenience rather than having to find the root.
/// A sketche's nodes can be labeled by a type T.
pub struct Sketch<T> {
    /// The entry node which represents the type of this sketch.
    pub entry: NodeIndex,
    /// The graph rooted by entry. This graph is prefix closed.
    pub graph: Graph<T, FieldLabel>,
}

/// A constraint graph quotiented over a symmetric subtyping relation.
pub struct SketchGraph<T> {
    quotient_graph: Graph<T, FieldLabel>,
    dtv_to_group: Rc<HashMap<DerivedTypeVar, NodeIndex>>,
}

// an equivalence between eq nodes implies an equivalence between edge
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
struct EdgeImplication {
    eq: (NodeIndex, NodeIndex),
    edge: (NodeIndex, NodeIndex),
}

impl<T: Clone> SketchGraph<T> {
    fn get_graph_for_idx(&self, root: NodeIndex) -> Sketch<T> {
        let dfs = Dfs::new(&self.quotient_graph, root);
        let mut reachable_subgraph: Graph<T, _> = Graph::new();
        let reachable: Vec<_> = dfs.iter(&self.quotient_graph).collect();
        let node_map = reachable
            .iter()
            .map(|old| {
                let new = reachable_subgraph
                    .add_node(self.quotient_graph.node_weight(*old).unwrap().clone());
                (*old, new)
            })
            .collect::<HashMap<_, _>>();
        reachable
            .iter()
            .for_each(|x| self.add_edges_to_subgraph(*x, &node_map, &mut reachable_subgraph));

        Sketch {
            entry: *node_map.get(&root).unwrap(),
            graph: reachable_subgraph,
        }
    }

    /// Gets the reachable sketch for a derived type variable if it exists in the constraing graph.
    pub fn get_sketch_for_dtv(&self, dtv: &DerivedTypeVar) -> Option<Sketch<T>> {
        self.dtv_to_group
            .get(dtv)
            .map(|x| self.get_graph_for_idx(*x))
    }

    /// Gets the representing node index for the given tvar if it exists
    pub fn get_node_index_for_variable(&self, dtv: &DerivedTypeVar) -> Option<NodeIndex> {
        self.dtv_to_group.get(dtv).cloned()
    }
}

impl<T> SketchGraph<T> {
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

    fn add_edges_to_subgraph<O>(
        &self,
        start: NodeIndex,
        node_map: &HashMap<NodeIndex, NodeIndex>,
        subgraph: &mut Graph<O, FieldLabel>,
    ) {
        for e in self
            .quotient_graph
            .edges_directed(start, petgraph::EdgeDirection::Outgoing)
        {
            subgraph.add_edge(
                *node_map.get(&e.source()).unwrap(),
                *node_map.get(&e.target()).unwrap(),
                e.weight().clone(),
            );
        }
    }

    /// Creates a quotiented sketch graph from a constraint set.
    pub fn new(s: &ConstraintSet) -> SketchGraph<()> {
        let mut nd = NodeDefinedGraph::new();

        Self::dts_from_constraint_set(s)
            .cloned()
            .for_each(|f| Self::insert_dtv(&mut nd, f));

        let labeled = Self::quoetient_graph(&nd, s);
        let quotient_graph = nd.quoetient_graph(&labeled);

        let old_to_new: HashMap<NodeIndex, NodeIndex> = quotient_graph
            .get_graph()
            .node_references()
            .map(|(idx, child_node)| child_node.iter().map(move |child| (*child, idx)))
            .flatten()
            .collect();

        let mapping = nd
            .nodes
            .iter()
            .map(|(dtv, old_idx)| (dtv.clone(), *old_to_new.get(old_idx).unwrap()));

        let new_quotient_graph = quotient_graph
            .get_graph()
            .clone()
            .map(|_, _| (), |_, e| e.clone());
        SketchGraph {
            quotient_graph: new_quotient_graph,
            dtv_to_group: Rc::new(mapping.collect()),
        }
    }

    /// Produces a new graph by mapping F accross the nodes.
    pub fn map_nodes<F, U: Clone>(&self, mut f: F) -> SketchGraph<U>
    where
        F: FnMut(NodeIndex, &T) -> U,
    {
        SketchGraph {
            quotient_graph: self.quotient_graph.map(|x, y| f(x, y), |_, e| e.clone()),
            dtv_to_group: self.dtv_to_group.clone(),
        }
    }

    /// Gets a reference to the underlying graph
    pub fn get_graph(&self) -> &Graph<T, FieldLabel> {
        &self.quotient_graph
    }
}

/// The context under which a labeling of sketches can be computed. Based on subtyping constraints
/// Sketch nodes will be lableed by computing joins and meets of euqivalence relations.
pub struct LabelingContext<'a, U: NamedLatticeElement, T: NamedLattice<U>> {
    lattice: &'a T,
    nm: std::marker::PhantomData<U>,
    type_lattice_elements: HashSet<TypeVariable>,
}

impl<'a, U: NamedLatticeElement, T: NamedLattice<U>> LabelingContext<'a, U, T> {
    /// Creates a new lattice context described by the named lattice itself which returns the lattice elem for a given string type var
    /// and the set of available elements.
    pub fn new(lattice: &'a T, elements: HashSet<TypeVariable>) -> Self {
        Self {
            lattice,
            type_lattice_elements: elements,
            nm: PhantomData,
        }
    }

    fn apply_variance<O>(&self, orig_graph: &Graph<O, FieldLabel>) -> HashMap<NodeIndex, U> {
        let mut labeling: HashMap<NodeIndex, U> = HashMap::new();
        // Stores who we visited and how we visited them.
        let mut visited: HashMap<NodeIndex, Vec<FieldLabel>> = HashMap::new();

        let mut to_visit = Vec::new();
        let roots = Self::get_roots(orig_graph);
        roots.iter().for_each(|x| to_visit.push((*x, Vec::new())));

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

        visited
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
            .for_each(|(new_nd_index, var)| {
                labeling.insert(
                    new_nd_index,
                    match var {
                        Variance::Covariant => self.lattice.top(),
                        Variance::Contravariant => self.lattice.bot(),
                    },
                );
            });

        labeling
    }

    fn get_roots<N, E, Ty: EdgeType, Ix: IndexType>(
        tgt: &Graph<N, E, Ty, Ix>,
    ) -> Vec<NodeIndex<Ix>> {
        // make weights idxs so we can select an index from the scc
        let ngraph = tgt.map(|idx, _y| idx, |_, _| ());

        let condens = algo::condensation(ngraph, true);

        condens
            .node_identifiers()
            .filter(|x| {
                condens
                    .neighbors_directed(*x, petgraph::EdgeDirection::Incoming)
                    .count()
                    == 0
            })
            .map(|scc_idx| {
                // This scc is a root
                let orig_idxs = condens.node_weight(scc_idx).unwrap();
                // There should not be zero node sccs
                assert!(!orig_idxs.is_empty());
                // any node from an scc can work as the root so just take the first one we saw
                *orig_idxs.get(0).unwrap()
            })
            .collect()
    }

    fn get_initial_labels<O: Clone>(&self, initial_sketches: &SketchGraph<O>) -> SketchGraph<U> {
        let lab = self.apply_variance(&initial_sketches.quotient_graph);

        initial_sketches.map_nodes(|nd_idx, _old_weight| lab.get(&nd_idx).unwrap().clone())
    }

    /// Creates a fully labeled sketch graph
    pub fn create_labeled_sketchgraph<O: Clone>(
        &self,
        cons: &ConstraintSet,
        initial_sketches: &SketchGraph<O>,
    ) -> SketchGraph<U> {
        let mut init = self.get_initial_labels(initial_sketches);
        self.label_sketches(cons, &mut init);
        init
    }

    fn dtv_is_uninterpreted_lattice(&self, dtv: &DerivedTypeVar) -> bool {
        self.type_lattice_elements.contains(dtv.get_base_variable())
            && dtv.get_field_labels().is_empty()
    }

    fn update_lattice_node(
        grph: &mut SketchGraph<U>,
        lattice_elem: U,
        target_dtv: &DerivedTypeVar,
        operation: impl Fn(&U, &U) -> U,
    ) {
        let target_group_idx = *grph.dtv_to_group.get(target_dtv).unwrap();
        let orig_value = grph
            .quotient_graph
            .node_weight_mut(target_group_idx)
            .unwrap();
        *orig_value = operation(orig_value, &lattice_elem);
    }

    /// Provided sketches labeled by equivalence class node indeces, computes a labeling of each node by the given lattice and constraint set.
    pub fn label_sketches(&self, cons: &ConstraintSet, sgraph: &mut SketchGraph<U>) {
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
                    && sgraph.dtv_to_group.contains_key(&subty.rhs)
                {
                    Self::update_lattice_node(
                        sgraph,
                        self.lattice
                            .get_elem(subty.lhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.rhs,
                        |x: &U, y: &U| x.join(y),
                    );
                } else if self.dtv_is_uninterpreted_lattice(&subty.rhs)
                    && sgraph.dtv_to_group.contains_key(&subty.lhs)
                {
                    Self::update_lattice_node(
                        sgraph,
                        self.lattice
                            .get_elem(subty.rhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.lhs,
                        |x: &U, y: &U| x.meet(y),
                    );
                }
            });
    }
}
