use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    hash::Hash,
};

use alga::general::{AbstractMagma, Additive};

use itertools::Itertools;
use petgraph::{
    data::{Build, DataMap},
    graph::{EdgeIndex, NodeIndex},
    stable_graph::StableDiGraph,
    visit::{Dfs, IntoEdgeReferences, IntoEdges, IntoEdgesDirected, IntoNodeReferences, Walker},
    EdgeDirection::Outgoing,
};

use petgraph::visit::EdgeRef;

use crate::solver::dfa_operations::DFA;
use crate::{constraints::DerivedTypeVar, solver::dfa_operations::Alphabet};

use super::{explore_paths, find_node};

// TODO(ian): use this abstraction for the transducer
/// A mapping graph allows the lookup of nodes by a hashable element. A node can also be queried for which hashable element it represents.
/// ie. there is an injective relationship between node indices and hashable elements.
#[derive(Clone)]
pub struct MappingGraph<W, N, E> {
    grph: StableDiGraph<W, E>,
    nodes: HashMap<N, NodeIndex>,
    reprs_to_graph_node: HashMap<NodeIndex, BTreeSet<N>>,
}

impl<W, N, E> MappingGraph<W, N, E> {
    /// Produces an unlabeled mapping graph from a DFA, actually we should just take the stable digraph here.
    pub fn from_dfa_and_labeling(dfa: StableDiGraph<W, E>) -> MappingGraph<W, N, E> {
        MappingGraph {
            grph: dfa,
            nodes: HashMap::new(),
            reprs_to_graph_node: HashMap::new(),
        }
    }
}

impl<W, N, E> MappingGraph<W, N, E>
where
    W: Clone,
    E: Clone,
    N: Clone + std::cmp::Eq + Hash,
{
    pub fn get_reachable_subgraph(&self, idx: NodeIndex) -> MappingGraph<W, N, E> {
        let reachable_idxs: BTreeSet<_> = Dfs::new(&self.grph, idx).iter(&self.grph).collect();
        let filtered_grph = self.grph.filter_map(
            |idx, nd| {
                if reachable_idxs.contains(&idx) {
                    Some(nd.clone())
                } else {
                    None
                }
            },
            |_e, w| Some(w.clone()),
        );

        let filtered_nodes = self
            .nodes
            .iter()
            .filter(|(k, v)| reachable_idxs.contains(v))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        let filtered_reprs = self
            .reprs_to_graph_node
            .iter()
            .filter(|(idx, _associated_nodes)| reachable_idxs.contains(idx))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        MappingGraph {
            grph: filtered_grph,
            nodes: filtered_nodes,
            reprs_to_graph_node: filtered_reprs,
        }
    }
}

// we can only quotient the graph if the weight is mergeable
impl<
        W: AbstractMagma<Additive> + std::cmp::PartialEq,
        N: Clone + Hash + Eq + Ord,
        E: Hash + Eq + Clone,
    > MappingGraph<W, N, E>
{
    pub fn replace_node(&mut self, key: N, grph: MappingGraph<W, N, E>) {
        let orig_var_idx = *self
            .get_node(&key)
            .expect("Should have node for replacement key");
        let reached_graph = self.get_reachable_subgraph(orig_var_idx);

        let nodes = reached_graph
            .nodes
            .iter()
            .map(|(_nd, idx)| *idx)
            .collect::<BTreeSet<NodeIndex>>();

        // Nodes are looked up by their original path. Since we always refine the original type we should be able to follow a path from the original
        // tvar in the refined tvar.
        let edges_outside_subgraph = explore_paths(&self.grph, orig_var_idx)
            .map(|(pth, reached_id)| {
                let incoming_edges = self
                    .get_graph()
                    .edges_directed(reached_id, petgraph::EdgeDirection::Incoming);

                incoming_edges
                    .filter_map(|orig_e| {
                        assert!(orig_e.source() != reached_id);
                        if nodes.contains(&orig_e.source()) {
                            //internal _edge
                            None
                        } else {
                            Some((orig_e.weight().clone(), orig_e.source(), pth.clone()))
                        }
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .flatten()
            .collect::<Vec<_>>();

        // remove reached nodes
        nodes.iter().for_each(|nd| {
            self.remove_node_by_idx(*nd);
        });
        // insert new nodes getting ids
        let mut old_idx_to_new_idx_mapping = HashMap::new();

        let mut add_node = |target_idx| {
            *old_idx_to_new_idx_mapping
                .entry(target_idx)
                .or_insert_with(|| {
                    let weight = grph.get_graph().node_weight(target_idx).unwrap().clone();
                    let grp = grph.get_group_for_node(target_idx);
                    if let Some(repr) = grp.iter().next() {
                        let idx = self.add_node(repr.clone(), weight);
                        for elem in grp.iter() {
                            self.merge_nodes(repr.clone(), elem.clone());
                        }
                        idx
                    } else {
                        self.grph.add_node(weight)
                    }
                })
        };
        grph.get_graph()
            .node_indices()
            .map(|nd| {
                let src = add_node(nd);
                let mut tot = Vec::new();
                for edge in grph.get_graph().edges_directed(src, Outgoing) {
                    let dst = add_node(edge.target());
                    tot.push((src, edge.weight().clone(), dst));
                }
                tot.into_iter()
            })
            .flatten()
            .collect::<Vec<_>>()
            .into_iter()
            .for_each(|(src, wt, dst)| {
                self.grph.add_edge(src, dst, wt);
            });

        // add edges into subgraph
        edges_outside_subgraph.into_iter().for_each(
            |(edge_weight, src_node, nd_in_subgraph_pth)| {
                if let Some(old_idx) = find_node(
                    grph.get_graph(),
                    *grph
                        .get_node(&key)
                        .expect("replacing graph should represent node being replaced"),
                    nd_in_subgraph_pth.iter().map(|e_index| {
                        grph.grph
                            .edge_weight(*e_index)
                            .expect("edge references should be valid")
                    }),
                ) {
                    let new_idx = old_idx_to_new_idx_mapping
                        .get(&old_idx)
                        .expect("all old idxs should be added");
                    self.grph.add_edge(src_node, *new_idx, edge_weight);
                }
            },
        );
        // Canonicalize(preserve invariant that no two equal outgoing edges without merging nodes)
    }

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

                for (_src, dst, weight) in self
                    .grph
                    .edges_directed(fst, petgraph::EdgeDirection::Outgoing)
                    .map(|e| (e.source(), e.target(), e.weight().clone()))
                    .collect::<Vec<_>>()
                {
                    self.add_edge(new_idx, dst, weight);
                }

                for (src, _dst, weight) in self
                    .grph
                    .edges_directed(fst, petgraph::EdgeDirection::Incoming)
                    .map(|e| (e.source(), e.target(), e.weight().clone()))
                    .collect::<Vec<_>>()
                {
                    self.add_edge(src, new_idx, weight);
                }

                for (_src, dst, weight) in self
                    .grph
                    .edges_directed(snd, petgraph::EdgeDirection::Outgoing)
                    .map(|e| (e.source(), e.target(), e.weight().clone()))
                    .collect::<Vec<_>>()
                {
                    self.add_edge(new_idx, dst, weight);
                }

                for (src, _dst, weight) in self
                    .grph
                    .edges_directed(snd, petgraph::EdgeDirection::Incoming)
                    .map(|e| (e.source(), e.target(), e.weight().clone()))
                    .collect::<Vec<_>>()
                {
                    self.add_edge(src, new_idx, weight);
                }

                self.grph.remove_node(fst);
                self.grph.remove_node(snd);
            }
            (Some(_fst), Some(_snd)) => (),
        }
    }

    pub fn remove_node_by_idx(&mut self, idx: NodeIndex) -> Option<W> {
        let nd_set = self.reprs_to_graph_node.remove(&idx);
        if let Some(nd_set) = nd_set {
            for nd in nd_set {
                self.nodes.remove(&nd);
            }
        }

        self.grph.remove_node(idx)
    }

    pub fn remove_node(&mut self, node: &N) -> Option<W> {
        let idx = self.nodes.get(node);
        if let Some(&idx) = idx {
            let mapping = self
                .reprs_to_graph_node
                .get_mut(&idx)
                .expect("idx should have group");

            mapping.remove(node);
            self.nodes.remove(node);

            let wt = self
                .grph
                .node_weight(idx)
                .expect("node should have weight")
                .clone();

            if mapping.is_empty() {
                self.reprs_to_graph_node.remove(&idx);
                self.grph.remove_node(idx);
            }

            Some(wt)
        } else {
            None
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

            let src_node = *nd
                .get_node(repr_src)
                .expect("All nodes should be added to the graph");
            let dst_node = *nd
                .get_node(repr_dst)
                .expect("All nodes should be added to the graph");
            nd.add_edge(src_node, dst_node, edge.weight().clone());
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

impl<W: std::cmp::PartialEq + Clone, N: Clone + Hash + Eq + Ord, E: Hash + Eq + Clone>
    MappingGraph<W, N, E>
{
    pub fn relable_representative_nodes(
        &self,
        mapping: HashMap<N, NodeIndex>,
    ) -> MappingGraph<W, N, E> {
        // construct set

        let mut index_to_reprs = HashMap::new();
        mapping.iter().for_each(|(nd, idx)| {
            index_to_reprs
                .entry(*idx)
                .or_insert_with(|| BTreeSet::new())
                .insert(nd.clone());
        });

        MappingGraph {
            grph: self.grph.clone(),
            nodes: mapping,
            reprs_to_graph_node: index_to_reprs,
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
