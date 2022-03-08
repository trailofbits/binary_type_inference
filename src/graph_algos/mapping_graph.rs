use std::{
    collections::{BTreeSet, HashMap},
    hash::Hash,
};

use alga::general::{AbstractMagma, Additive};
use petgraph::{
    data::Build,
    graph::{EdgeIndex, NodeIndex},
    stable_graph::StableDiGraph,
    visit::{IntoEdgeReferences, IntoEdges},
};

use petgraph::visit::EdgeRef;

use crate::constraints::DerivedTypeVar;

// TODO(ian): use this abstraction for the transducer
/// A mapping graph allows the lookup of nodes by a hashable element. A node can also be queried for which hashable element it represents.
/// ie. there is a bijection menatined between node indices and the mapping elements.
#[derive(Clone)]
pub struct MappingGraph<W: std::cmp::PartialEq, N: Clone + Hash + Eq + Ord, E: Hash + Eq> {
    grph: StableDiGraph<W, E>,
    nodes: HashMap<N, NodeIndex>,
    reprs_to_graph_node: HashMap<NodeIndex, BTreeSet<N>>,
}

// we can only quotient the graph if the weight is mergeable
impl<
        W: AbstractMagma<Additive> + std::cmp::PartialEq,
        N: Clone + Hash + Eq + Ord,
        E: Hash + Eq + Clone,
    > MappingGraph<W, N, E>
{
    pub fn add_node(&mut self, key: N, weight: W) -> NodeIndex {
        if let Some(x) = self.nodes.get(&key) {
            let old_weight = self.grph.node_weight_mut(*x).unwrap();
            *old_weight = old_weight.operate(&weight);
            *x
        } else {
            let nd = self.grph.add_node(weight);
            self.nodes.insert(key.clone(), nd);
            self.reprs_to_graph_node
                .entry(nd)
                .or_insert_with(|| BTreeSet::new())
                .insert(key);
            nd
        }
    }

    fn update_all_children_of_idx_to(&mut self, old_idx: NodeIndex, new_idx: NodeIndex) {
        let old_set = self
            .reprs_to_graph_node
            .entry(old_idx)
            .or_insert_with(|| BTreeSet::new())
            .clone();

        let new_set = self
            .reprs_to_graph_node
            .entry(new_idx)
            .or_insert_with(|| BTreeSet::new());

        for v in old_set.iter() {
            self.nodes.insert(v.clone(), new_idx);
            new_set.insert(v.clone());
        }

        self.reprs_to_graph_node.remove(&old_idx);
    }

    pub fn merge_nodes(&mut self, key1: N, key2: N) {
        match (
            self.nodes.get(&key1).cloned(),
            self.nodes.get(&key2).cloned(),
        ) {
            (None, None) => (),
            (None, Some(x)) => {
                self.nodes.insert(key1.clone(), x);
                self.reprs_to_graph_node
                    .entry(x)
                    .or_insert_with(|| BTreeSet::new())
                    .insert(key1);
            }
            (Some(x), None) => {
                self.nodes.insert(key2.clone(), x);
                self.reprs_to_graph_node
                    .entry(x)
                    .or_insert_with(|| BTreeSet::new())
                    .insert(key2);
            }
            (Some(fst), Some(snd)) if fst != snd => {
                let new_weight = self
                    .grph
                    .node_weight(fst)
                    .unwrap()
                    .operate(self.grph.node_weight(snd).unwrap());

                let new_idx = self.grph.add_node(new_weight);

                self.update_all_children_of_idx_to(fst, new_idx);
                self.update_all_children_of_idx_to(snd, new_idx);

                for (src, dst, weight) in self
                    .grph
                    .edges(fst)
                    .map(|e| (e.target(), e.source(), e.weight().clone()))
                    .collect::<Vec<_>>()
                {
                    if src == fst {
                        // outgoing
                        self.add_edge(new_idx, dst, weight);
                    } else {
                        // incoming
                        self.add_edge(src, new_idx, weight);
                    }
                }

                for (src, dst, weight) in self
                    .grph
                    .edges(snd)
                    .map(|e| (e.target(), e.source(), e.weight().clone()))
                    .collect::<Vec<_>>()
                {
                    if src == snd {
                        // outgoing
                        self.add_edge(new_idx, dst, weight);
                    } else {
                        // incoming
                        self.add_edge(src, new_idx, weight);
                    }
                }

                self.grph.remove_node(fst);
                self.grph.remove_node(snd);
            }
            (Some(_fst), Some(_snd)) => (),
        }
    }

    /// Note it is invalid to pass this function an empty group
    pub fn quoetient_graph(&self, groups: &[BTreeSet<NodeIndex>]) -> MappingGraph<W, N, E> {
        let mut nd: MappingGraph<W, BTreeSet<NodeIndex>, E> = MappingGraph::new();

        let repr_mapping = groups
            .iter()
            .enumerate()
            .map(|(repr_indx, s)| s.iter().map(move |node_idx| (node_idx, repr_indx)))
            .flatten()
            .collect::<HashMap<_, _>>();

        for grp in groups.iter() {
            if !grp.is_empty() {
                let new_weight = grp
                    .iter()
                    .map(|idx| self.grph.node_weight(*idx).unwrap().clone())
                    .reduce(|fst, s| fst.operate(&s))
                    .expect("Group should be non empty");

                let _new_node = nd.add_node(grp.clone(), new_weight);
            }
        }

        for edge in self.get_graph().edge_references() {
            let repr_src = &groups[*repr_mapping.get(&edge.source()).unwrap()];
            let repr_dst = &groups[*repr_mapping.get(&edge.target()).unwrap()];

            let src_node = nd
                .get_node(repr_src)
                .expect("All nodes should be added to the graph");
            let dst_node = nd
                .get_node(repr_dst)
                .expect("All nodes should be added to the graph");
            nd.add_edge(*src_node, *dst_node, edge.weight().clone());
        }

        let new_mapping = self
            .nodes
            .iter()
            .map(|(orig_label, y)| {
                let new_idx = nd
                    .get_node(&groups[*repr_mapping.get(y).unwrap()])
                    .expect("All nodes should be added to the graph");
                (orig_label.clone(), *new_idx)
            })
            .collect::<HashMap<_, _>>();

        let mut new_rev_mapping: HashMap<NodeIndex, BTreeSet<N>> = HashMap::new();

        new_mapping.iter().for_each(|(n, idx)| {
            let b = new_rev_mapping
                .entry(*idx)
                .or_insert_with(|| BTreeSet::new());
            b.insert(n.clone());
        });

        MappingGraph {
            grph: nd.grph,
            nodes: new_mapping,
            reprs_to_graph_node: new_rev_mapping,
        }
    }
}

impl<W: std::cmp::PartialEq, N: Clone + Hash + Eq + Ord, E: Hash + Eq> MappingGraph<W, N, E> {
    pub fn new() -> MappingGraph<W, N, E> {
        MappingGraph {
            grph: StableDiGraph::new(),
            nodes: HashMap::new(),
            reprs_to_graph_node: HashMap::new(),
        }
    }

    pub fn get_group_for_node(&self, idx: NodeIndex) -> BTreeSet<N> {
        self.reprs_to_graph_node
            .get(&idx)
            .cloned()
            .unwrap_or(BTreeSet::new())
    }

    pub fn get_graph(&self) -> &StableDiGraph<W, E> {
        &self.grph
    }

    pub fn get_graph_mut(&mut self) -> &mut StableDiGraph<W, E> {
        &mut self.grph
    }

    pub fn get_node_mapping(&self) -> &HashMap<N, NodeIndex> {
        &self.nodes
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
}
