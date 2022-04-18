use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use alga::general::{AbstractMagma, Additive};

use itertools::Itertools;
use petgraph::{
    data::{Build, DataMap},
    graph::{EdgeIndex, NodeIndex},
    stable_graph::StableDiGraph,
    visit::{Dfs, IntoEdgeReferences, IntoEdges, IntoEdgesDirected, IntoNodeReferences, Walker},
    Directed,
    EdgeDirection::Outgoing,
};

use petgraph::visit::EdgeRef;

use crate::solver::dfa_operations::DFA;
use crate::{constraints::DerivedTypeVar, solver::dfa_operations::Alphabet};

use super::{explore_paths, find_node};

// TODO(ian): use this abstraction for the transducer
/// A mapping graph allows the lookup of nodes by a hashable element. A node can also be queried for which hashable element it represents.
#[derive(Clone)]
pub struct MappingGraph<W, N, E> {
    grph: StableDiGraph<W, E>,
    nodes: HashMap<N, NodeIndex>,
    reprs_to_graph_node: HashMap<NodeIndex, BTreeSet<N>>,
}

impl<W, N: Debug, E> MappingGraph<W, N, E> {
    /// Produces an unlabeled mapping graph from a DFA, actually we should just take the stable digraph here.
    pub fn from_dfa_and_labeling(dfa: StableDiGraph<W, E>) -> MappingGraph<W, N, E> {
        MappingGraph {
            grph: dfa,
            nodes: HashMap::new(),
            reprs_to_graph_node: HashMap::new(),
        }
    }

    /// Clean up the mapping graph to only keep around parts of the graph that are reachable from a label (we dont care about anything not reacable because we only need to type vars)
    pub fn remove_nodes_unreachable_from_label(&mut self) {
        let stack = self.nodes.values().cloned().collect::<Vec<_>>();

        let mut dfs = Dfs::from_parts(stack, HashSet::new());
        let mut reached = BTreeSet::new();
        while let Some(nx) = dfs.next(&self.grph) {
            reached.insert(nx);
        }

        for unreached_idx in self
            .grph
            .node_indices()
            .filter(|x| !reached.contains(x))
            .collect::<Vec<_>>()
        {
            // NOTE(Ian): ok to remove since it isnt labeled
            self.grph.remove_node(unreached_idx);
        }
    }
}

impl<W, N, E> MappingGraph<W, N, E>
where
    W: Clone,
    E: Clone,
    N: Clone + std::cmp::Eq + Hash,
{
    fn get_reachable_idxs(&self, idx: NodeIndex) -> BTreeSet<NodeIndex> {
        Dfs::new(&self.grph, idx).iter(&self.grph).collect()
    }

    pub fn get_reachable_subgraph(&self, idx: NodeIndex) -> MappingGraph<W, N, E> {
        let reachable_idxs: BTreeSet<_> = self.get_reachable_idxs(idx);
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

impl<
        W: AbstractMagma<Additive> + std::cmp::PartialEq,
        N: Clone + Hash + Eq + Ord + Display + Debug,
        E: Hash + Eq + Clone,
    > MappingGraph<W, N, E>
{
    pub fn replace_node(&mut self, key: N, grph: MappingGraph<W, N, E>) {
        let orig_var_idx = *self
            .get_node(&key)
            .expect("Should have node for replacement key");
        let nodes = self.get_reachable_idxs(orig_var_idx);

        // Nodes are looked up by their original path. Since we always refine the original type we should be able to follow a path from the original
        // tvar in the refined tvar.
        let edges_outside_subgraph: Vec<(E, NodeIndex, Vec<E>)> =
            explore_paths(&self.grph, orig_var_idx)
                .map(|(pth, reached_id)| {
                    let incoming_edges = self
                        .get_graph()
                        .edges_directed(reached_id, petgraph::EdgeDirection::Incoming);

                    incoming_edges
                        .filter_map(|orig_e| {
                            // TODO(Ian): saw a reflexive edge in the original graph... why?
                            assert!(orig_e.source() != reached_id);
                            if nodes.contains(&orig_e.source()) {
                                //internal _edge
                                None
                            } else {
                                Some((
                                    orig_e.weight().clone(),
                                    orig_e.source(),
                                    pth.iter()
                                        .map(|eidx| {
                                            self.grph
                                                .edge_weight(*eidx)
                                                .expect("eid should be valid")
                                                .clone()
                                        })
                                        .collect(),
                                ))
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
            let new = *old_idx_to_new_idx_mapping
                .entry(target_idx)
                .or_insert_with(|| {
                    let weight = grph.get_graph().node_weight(target_idx).unwrap().clone();
                    self.grph.add_node(weight)
                });
            println!("{}", old_idx_to_new_idx_mapping.len());
            new
        };
        grph.get_graph()
            .node_indices()
            .map(|nd| {
                println!("Looking at nd {}", nd.index());
                let src = add_node(nd);
                let mut tot = Vec::new();
                for edge in grph.get_graph().edges_directed(nd, Outgoing) {
                    let dst = add_node(edge.target());
                    assert!(src != dst);
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

        assert!(old_idx_to_new_idx_mapping.len() > 0);
        // relabel ourselves to inclue the original labels
        // We dont need to merge because the labels are received from the graph we are replacing into so any labels inside the subgraph are not elsewhere
        let mut new_labeling = self.nodes.clone();

        for (old_idx, new_idx) in old_idx_to_new_idx_mapping.iter() {
            for n in grph.get_group_for_node(*old_idx) {
                assert!(!self.nodes.contains_key(&n));
                new_labeling.insert(n, *new_idx);
            }
        }
        self.inplace_relable_representative_nodes(new_labeling);

        // add edges into subgraph
        edges_outside_subgraph.into_iter().for_each(
            |(edge_weight, src_node, nd_in_subgraph_pth)| {
                if let Some(old_idx) = find_node(
                    grph.get_graph(),
                    *grph
                        .get_node(&key)
                        .expect("replacing graph should represent node being replaced"),
                    nd_in_subgraph_pth.iter(),
                ) {
                    let new_idx = old_idx_to_new_idx_mapping
                        .get(&old_idx)
                        .expect("all old idxs should be added");
                    assert!(src_node != *new_idx);
                    self.grph.add_edge(src_node, *new_idx, edge_weight);
                }
            },
        );
        // Canonicalize(preserve invariant that no two equal outgoing edges without merging nodes)
    }
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
        let mut nd = StableDiGraph::new();

        let repr_mapping = groups
            .iter()
            .enumerate()
            .map(|(repr_indx, s)| s.iter().map(move |node_idx| (node_idx, repr_indx)))
            .flatten()
            .collect::<HashMap<_, _>>();

        let mut group_to_new_node = HashMap::new();

        for (i, grp) in groups.iter().enumerate() {
            println!("{}", i);
            if !grp.is_empty() {
                let new_weight = grp
                    .iter()
                    .map(|idx| self.grph.node_weight(*idx).unwrap().clone())
                    .reduce(|fst, s| fst.operate(&s))
                    .expect("Group should be non empty");

                let new_node_repr = nd.add_node(new_weight);
                group_to_new_node.insert(i, new_node_repr);
            }
        }

        let mut eset = HashSet::new();
        for edge in self.get_graph().edge_references() {
            let repr_src = group_to_new_node
                .get(repr_mapping.get(&edge.source()).unwrap())
                .unwrap();
            let repr_dst = group_to_new_node
                .get(repr_mapping.get(&edge.target()).unwrap())
                .unwrap();
            let e = (*repr_src, *repr_dst, edge.weight().clone());
            if !eset.contains(&e) {
                nd.add_edge(e.0, e.1, e.2.clone());
                eset.insert(e);
            }
        }

        let new_mapping = self
            .nodes
            .iter()
            .map(|(orig_label, y)| {
                let new_idx = group_to_new_node.get(repr_mapping.get(y).unwrap()).unwrap();

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
            grph: nd,
            nodes: new_mapping,
            reprs_to_graph_node: new_rev_mapping,
        }
    }
}

impl<W: std::cmp::PartialEq + Clone, N: Clone + Hash + Eq + Ord, E: Hash + Eq + Clone>
    MappingGraph<W, N, E>
{
    fn inplace_relable_representative_nodes(&mut self, mapping: HashMap<N, NodeIndex>) {
        let mut index_to_reprs = HashMap::new();
        mapping.iter().for_each(|(nd, idx)| {
            index_to_reprs
                .entry(*idx)
                .or_insert_with(|| BTreeSet::new())
                .insert(nd.clone());
        });

        self.nodes = mapping;
        self.reprs_to_graph_node = index_to_reprs;
    }

    /// Takes a mapping of reprs to node indices to relable the graph
    pub fn relable_representative_nodes(
        &self,
        mapping: HashMap<N, NodeIndex>,
    ) -> MappingGraph<W, N, E> {
        // construct set
        let mut new_graph = self.clone();
        new_graph.inplace_relable_representative_nodes(mapping);
        return new_graph;
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
