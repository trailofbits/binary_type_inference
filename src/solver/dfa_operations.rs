use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    hash::Hash,
};

use itertools::Itertools;
use petgraph::{
    graph::NodeIndex,
    visit::{Dfs, Walker},
    Directed, Graph,
};

pub trait Alphabet: Hash + Eq + Ord + Clone {}

pub type Indices = Vec<usize>;

/// So... to support DFAs with infinite alphabets we do some sketch stuff. If an edge does not exist for some alphabe symbol we assume it leads to a reject state.
pub trait DFA<T>
where
    T: Alphabet,
{
    fn entry(&self) -> usize;
    fn accept_indices(&self) -> Indices;
    fn all_indices(&self) -> Indices;
    fn dfa_edges(&self) -> Vec<(usize, T, usize)>;
}

struct IdContext<T> {
    cid: usize,
    mp: HashMap<T, usize>,
}

impl<T: Hash + Eq> IdContext<T> {
    pub fn get_node(&mut self, nd: T) -> usize {
        if let Some(x) = self.mp.get(&nd) {
            *x
        } else {
            let id = self.cid;
            self.cid += 1;
            self.mp.insert(nd, id);
            id
        }
    }
}

impl<T> Default for IdContext<T> {
    fn default() -> Self {
        Self {
            cid: Default::default(),
            mp: Default::default(),
        }
    }
}

type DFAEdgeMap<A> = BTreeMap<usize, BTreeMap<A, usize>>;

fn create_edge_map<A, T>(dfa: &T) -> BTreeMap<usize, BTreeMap<A, usize>>
where
    A: Alphabet,
    T: DFA<A>,
{
    let mut mp: BTreeMap<usize, BTreeMap<A, usize>> = BTreeMap::new();
    for (src, s, dst) in dfa.dfa_edges() {
        let amap = mp.entry(src).or_insert_with(|| BTreeMap::new());
        amap.insert(s, dst);
    }
    mp
}

struct ExplicitDFA<A> {
    ent_id: usize,
    edges: BTreeSet<(usize, A, usize)>,
    accept_indexes: BTreeSet<usize>,
    all_indeces: BTreeSet<usize>,
}

impl<A: Alphabet> DFA<A> for ExplicitDFA<A> {
    fn entry(&self) -> usize {
        self.ent_id
    }

    fn accept_indices(&self) -> Indices {
        self.accept_indexes.iter().cloned().collect()
    }

    fn all_indices(&self) -> Indices {
        self.all_indeces.iter().cloned().collect()
    }

    fn dfa_edges(&self) -> Vec<(usize, A, usize)> {
        self.edges.iter().cloned().collect()
    }
}

/// For each node in a partition determines based on the transitions which set transitions occur
fn find_edge_set<A: Alphabet>(
    edges: &DFAEdgeMap<A>,
    // maps a node index to a part id.
    old_parts: &HashMap<usize, usize>,
    curr_part: &BTreeSet<usize>,
) -> Vec<(usize, BTreeSet<(A, usize)>)> {
    curr_part
        .iter()
        .map(|nd| {
            let def = BTreeMap::new();
            (
                *nd,
                edges
                    .get(nd)
                    .unwrap_or(&def)
                    .iter()
                    .map(|(a, x)| {
                        (
                            a.clone(),
                            *old_parts.get(x).expect("all nodes should have a partition"),
                        )
                    })
                    .collect::<BTreeSet<(A, usize)>>(),
            )
        })
        .collect()
}

/// Edge set to partition group
fn edge_set_to_partitions<A: Alphabet>(
    edges: Vec<(usize, BTreeSet<(A, usize)>)>,
) -> Vec<BTreeSet<usize>> {
    let mut prev_trans_map: HashMap<BTreeSet<(A, usize)>, BTreeSet<usize>> = HashMap::new();
    for (nd_id, transitions) in edges.into_iter() {
        let set = prev_trans_map
            .entry(transitions)
            .or_insert_with(|| BTreeSet::new());
        set.insert(nd_id);
    }

    prev_trans_map.into_iter().map(|(_, part)| part).collect()
}

fn find_new_partitions<A: Alphabet>(
    edges: &DFAEdgeMap<A>,
    // maps a node index to a part id.
    old_parts: &HashMap<usize, usize>,
    curr_part: &BTreeSet<usize>,
) -> Vec<BTreeSet<usize>> {
    edge_set_to_partitions(find_edge_set(edges, old_parts, curr_part))
}

fn partition_vector_to_id_map<'a>(
    it: impl Iterator<Item = &'a BTreeSet<usize>>,
) -> HashMap<usize, usize> {
    it.enumerate()
        .map(|(part_id, nd_set)| nd_set.iter().map(move |mem| (*mem, part_id)))
        .flatten()
        .collect()
}

/// Simple and ineffecient minimization of a DFA by building the Myhill–Nerode relation directly.
pub fn minimize<T, A>(lhs: &T) -> impl DFA<A>
where
    A: Alphabet,
    T: DFA<A>,
{
    let g = Graph::<(), (), Directed, usize>::from_edges(
        lhs.dfa_edges().into_iter().map(|e| (e.0, e.2)),
    );

    let reached_idxs: BTreeSet<usize> = Dfs::new(&g, NodeIndex::from(lhs.entry()))
        .iter(&g)
        .map(|idx| idx.index())
        .collect();

    let accepts = lhs
        .accept_indices()
        .into_iter()
        .filter(|x| reached_idxs.contains(x))
        .collect::<BTreeSet<usize>>();
    let rejects = lhs
        .all_indices()
        .into_iter()
        .filter(|x| !accepts.contains(x) && reached_idxs.contains(x))
        .collect::<BTreeSet<usize>>();

    let lhs_edge_map: DFAEdgeMap<A> = create_edge_map(lhs);

    let mut paritions: Vec<BTreeSet<usize>> = vec![accepts.clone(), rejects];

    loop {
        let mut new_partitions = Vec::new();

        let old_part_ids: HashMap<usize, usize> = partition_vector_to_id_map(paritions.iter());

        for part in paritions.iter() {
            new_partitions.extend(find_new_partitions(&lhs_edge_map, &old_part_ids, part));
        }

        if new_partitions.len() <= paritions.len() {
            break;
        } else {
            paritions = new_partitions;
        }
    }

    let mut cont: IdContext<BTreeSet<usize>> = IdContext::default();
    let part_id = partition_vector_to_id_map(paritions.iter());
    // I regret writing things this way, i apologize, flattens should occur earlier clones later
    let edges = paritions
        .iter()
        .map(|x| {
            let src_node = cont.get_node(x.clone());
            let ref_src = &src_node;
            x.iter()
                .map(|src| {
                    let emp = BTreeMap::new();
                    lhs_edge_map
                        .get(src)
                        .unwrap_or(&emp)
                        .iter()
                        .map(|(k, v)| {
                            (
                                *ref_src,
                                k.clone(),
                                cont.get_node(
                                    paritions[*part_id
                                        .get(v)
                                        .expect("every node should be in a partition")]
                                    .clone(),
                                ),
                            )
                        })
                        .collect::<Vec<_>>()
                        .into_iter()
                })
                .flatten()
                .collect::<Vec<_>>()
                .into_iter()
        })
        .flatten()
        .collect::<BTreeSet<_>>();

    let ent_node = cont.get_node(
        paritions[*part_id
            .get(&lhs.entry())
            .expect("should have partition for entry")]
        .clone(),
    );

    let all_nodes = paritions
        .iter()
        .map(|x| x.into_iter().cloned())
        .flatten()
        .collect::<BTreeSet<_>>();

    let all_accept_nodes = accepts
        .iter()
        .map(|x| {
            let part = *part_id
                .get(x)
                .expect("the accept node should be in a partition");
            cont.get_node(paritions[part].clone())
        })
        .collect::<BTreeSet<_>>();

    ExplicitDFA {
        ent_id: ent_node,
        edges,
        accept_indexes: all_accept_nodes,
        all_indeces: all_nodes,
    }
}

/// Product construction intersection of dfas
pub fn intersection<T, U, A>(lhs: &T, rhs: &U) -> impl DFA<A>
where
    A: Alphabet,
    T: DFA<A>,
    U: DFA<A>,
{
    let mut cont = IdContext::default();

    let lhs_edge_map = create_edge_map(lhs);
    let rhs_edge_map = create_edge_map(rhs);

    let ent_id = cont.get_node((lhs.entry(), rhs.entry()));

    let lhs_idxs = lhs.all_indices();

    let rhs_idxs = rhs.all_indices();

    let mut new_edges: BTreeSet<(usize, A, usize)> = BTreeSet::new();

    for (fst, snd) in lhs_idxs.iter().cartesian_product(rhs_idxs.clone()) {
        if let Some(edges) = lhs_edge_map.get(fst) {
            for (a, dst) in edges.iter() {
                if let Some(snd_edges) = rhs_edge_map.get(&snd) {
                    if let Some(snd_dst) = snd_edges.get(a) {
                        let new_src = cont.get_node((*fst, snd));
                        let new_dst = cont.get_node((*dst, *snd_dst));
                        new_edges.insert((new_src, a.clone(), new_dst));
                    }
                }
            }
        }
    }

    let accept_idxs_rhs = rhs.accept_indices();
    let accept_indexes: BTreeSet<usize> = lhs
        .accept_indices()
        .into_iter()
        .cartesian_product(accept_idxs_rhs)
        .map(|(fst, snd)| cont.get_node((fst, snd)))
        .collect();

    let all_indeces = lhs_idxs
        .iter()
        .cartesian_product(rhs_idxs)
        .map(|(lhs, rhs)| cont.get_node((*lhs, rhs)))
        .collect();

    ExplicitDFA {
        ent_id,
        edges: new_edges,
        accept_indexes,
        all_indeces,
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum UnionNodeType {
    Lhs,
    Rhs,
    Synthesized,
}

struct UnionContext {
    cont: IdContext<(usize, UnionNodeType)>,
    entry_lhs: usize,
    entry_rhs: usize,
}

impl UnionContext {
    fn get_node(
        &mut self,
        src_idx: usize,
        entry_idx: usize,
        normal_node_type: UnionNodeType,
    ) -> usize {
        if src_idx == entry_idx {
            self.cont.get_node((0, UnionNodeType::Synthesized))
        } else {
            self.cont.get_node((src_idx, normal_node_type))
        }
    }

    fn get_lhs_node(&mut self, src_idx: usize) -> usize {
        self.get_node(src_idx, self.entry_lhs, UnionNodeType::Lhs)
    }

    fn get_rhs_node(&mut self, src_idx: usize) -> usize {
        self.get_node(src_idx, self.entry_rhs, UnionNodeType::Rhs)
    }

    fn new(entry_lhs: usize, entry_rhs: usize) -> UnionContext {
        UnionContext {
            cont: IdContext::default(),
            entry_lhs,
            entry_rhs,
        }
    }
}

/// Unions the DFA by merging entry nodes
/// TODO(ian): this doesnt actually work because it creates an NFA
/// TODO(ian): do a product construction for the union instead
pub fn union<T, U, A>(lhs: &T, rhs: &U) -> impl DFA<A>
where
    A: Alphabet,
    T: DFA<A>,
    U: DFA<A>,
{
    let mut cont = UnionContext::new(lhs.entry(), rhs.entry());

    let mut copied_edges = lhs
        .dfa_edges()
        .into_iter()
        .map(|(src, a, dst)| (cont.get_lhs_node(src), a, cont.get_lhs_node(dst)))
        .collect::<BTreeSet<(usize, A, usize)>>();

    let rhs_edges = lhs
        .dfa_edges()
        .into_iter()
        .map(|(src, a, dst)| (cont.get_rhs_node(src), a, cont.get_rhs_node(dst)));

    copied_edges.extend(rhs_edges);

    //accepts are the union of previous accepts we also have to check if the entries were accepts
    let all_accepts = lhs
        .accept_indices()
        .into_iter()
        .map(|x| cont.get_lhs_node(x))
        .collect::<Vec<_>>()
        .into_iter()
        .chain(
            rhs.accept_indices()
                .into_iter()
                .map(|x| cont.get_rhs_node(x)),
        )
        .collect::<BTreeSet<_>>();

    let all_states = lhs
        .all_indices()
        .into_iter()
        .map(|x| cont.get_lhs_node(x))
        .collect::<Vec<_>>()
        .into_iter()
        .chain(rhs.all_indices().into_iter().map(|x| cont.get_rhs_node(x)))
        .collect::<BTreeSet<_>>();

    let ent_id = cont.get_lhs_node(lhs.entry());

    ExplicitDFA {
        ent_id,
        edges: copied_edges,
        accept_indexes: all_accepts,
        all_indeces: all_states,
    }
}

#[cfg(test)]
mod test {}
