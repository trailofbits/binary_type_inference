use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    hash::Hash,
    iter::FromIterator,
};

use itertools::Itertools;
use petgraph::{
    graph::NodeIndex,
    visit::{Dfs, Walker},
    Directed, Graph,
};

/// A supertrait representing the properties needed to be a DFA's alphabet.
pub trait Alphabet: Hash + Eq + Ord + Clone {}

/// Indices representing nodes in a DFA.
pub type Indices = Vec<usize>;

/// So... to support DFAs with infinite alphabets we do some sketch stuff. If an edge does not exist for some alphabe symbol we assume it leads to a reject state.
pub trait DFA<T>
where
    T: Alphabet,
{
    /// The entry index of the dfa.
    fn entry(&self) -> usize;

    /// The accepting indices of the dfa.
    fn accept_indices(&self) -> Indices;

    /// All indices in the dfa.
    fn all_indices(&self) -> Indices;

    /// For an edge (src, A, dst) src is the index of the src node, dst is the index of the destination, and A is the letter
    /// required to take that edge.
    fn dfa_edges(&self) -> Vec<(usize, T, usize)>;
}

struct IdContext<T> {
    cid: usize,
    mp: HashMap<T, usize>,
}

impl<T: Hash + Eq + Debug> IdContext<T> {
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

/// Represents a DFA as an explicit set of usize indices
pub struct ExplicitDFA<A> {
    /// Entry index
    pub ent_id: usize,
    /// Edges from (src, alphabet, dsts)
    pub edges: BTreeSet<(usize, A, usize)>,
    /// Accept indices
    pub accept_indexes: BTreeSet<usize>,
    /// Accept indices + reject indices
    pub all_indeces: BTreeSet<usize>,
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
            .or_insert_with(BTreeSet::new);
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
        .flat_map(|(part_id, nd_set)| nd_set.iter().map(move |mem| (*mem, part_id)))
        .collect()
}

fn get_reachable_idxs<T, A>(lhs: &T) -> BTreeSet<usize>
where
    A: Alphabet,
    T: DFA<A>,
{
    let g = Graph::<(), (), Directed, usize>::from_edges(
        lhs.dfa_edges().into_iter().map(|e| (e.0, e.2)),
    );

    let reached_idxs: BTreeSet<usize> = if g
        .node_indices()
        .collect::<BTreeSet<_>>()
        .contains(&NodeIndex::from(lhs.entry()))
    {
        Dfs::new(&g, NodeIndex::from(lhs.entry()))
            .iter(&g)
            .map(|idx| idx.index())
            .collect()
    } else {
        BTreeSet::from([lhs.entry()])
    };
    reached_idxs
}

/// Simple and ineffecient minimization of a DFA by building the Myhill–Nerode relation directly.
pub fn minimize<T, A>(lhs: &T) -> impl DFA<A>
where
    A: Alphabet,
    T: DFA<A>,
{
    let reached_idxs = get_reachable_idxs(lhs);
    let accepts = lhs
        .accept_indices()
        .into_iter()
        .filter(|x| reached_idxs.contains(x))
        .collect::<BTreeSet<usize>>();
    /*let rejects = lhs
    .all_indices()
    .into_iter()
    .filter(|x| !accepts.contains(x) && reached_idxs.contains(x))
    .collect::<BTreeSet<usize>>();*/

    let new_edges: BTreeSet<(usize, A, usize)> = lhs
        .dfa_edges()
        .into_iter()
        .filter(|(src, _, dst)| reached_idxs.contains(src) && reached_idxs.contains(dst))
        .map(|a| a.clone())
        .collect();
    /*
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
            .flat_map(|x| {
                let src_node = cont.get_node(x.clone());
                let ref_src = &src_node;
                x.iter()
                    .flat_map(|src| {
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
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .collect::<BTreeSet<_>>();

        let ent_node = cont.get_node(
            paritions[*part_id
                .get(&lhs.entry())
                .expect("should have partition for entry")]
            .clone(),
        );

        let all_nodes = paritions
            .iter()
            .filter_map(|part| {
                if !part.is_empty() {
                    Some(cont.get_node(part.clone()))
                } else {
                    None
                }
            })
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
    */
    ExplicitDFA {
        ent_id: lhs.entry(),
        edges: new_edges,
        accept_indexes: accepts,
        all_indeces: reached_idxs,
    }
}

/// Product construction intersection of dfas
pub fn intersection<T, U, A>(lhs: &T, rhs: &U) -> impl DFA<A>
where
    A: Alphabet,
    T: DFA<A>,
    U: DFA<A>,
{
    let new_dfa = cartesian_product_internal(lhs, rhs, false);

    minimize(&new_dfa)
}

fn cartesian_product_internal<T, U, A>(
    lhs: &T,
    rhs: &U,
    should_accept_nodes_with_one_reject: bool,
) -> impl DFA<A>
where
    A: Alphabet,
    T: DFA<A>,
    U: DFA<A>,
{
    assert!(!lhs.all_indices().is_empty());
    assert!(!rhs.all_indices().is_empty());
    let mut cont = IdContext::default();

    let lhs_edge_map = create_edge_map(lhs);
    let rhs_edge_map = create_edge_map(rhs);

    let ent_id = cont.get_node((lhs.entry(), rhs.entry()));

    let lhs_idxs = lhs.all_indices();

    let rhs_idxs = rhs.all_indices();

    let mut new_edges: BTreeSet<(usize, A, usize)> = BTreeSet::new();

    for (fst, snd) in lhs_idxs.iter().cartesian_product(rhs_idxs.clone()) {
        let emp_edge_map = BTreeMap::new();
        let lhs_edges = lhs_edge_map.get(fst).unwrap_or(&emp_edge_map);
        let rhs_edges = rhs_edge_map.get(&snd).unwrap_or(&emp_edge_map);

        for a in lhs_edges.keys().chain(rhs_edges.keys()) {
            let lhs_target = lhs_edges
                .get(a)
                .cloned()
                .expect("Every node should have an edge for each alphabet character in a DFA");
            let rhs_target = rhs_edges
                .get(a)
                .cloned()
                .expect("Every node should have an edge for each alphabet character in a DFA");

            let new_src = cont.get_node((*fst, snd));
            let new_dst = cont.get_node((lhs_target, rhs_target));
            new_edges.insert((new_src, a.clone(), new_dst));
        }
    }

    let accept_idxs_lhs = lhs.accept_indices();
    let accept_idxs_rhs = rhs.accept_indices();
    let accept_indexes: BTreeSet<usize> = if !should_accept_nodes_with_one_reject {
        accept_idxs_lhs
            .into_iter()
            .cartesian_product(accept_idxs_rhs)
            .map(|(fst, snd)| cont.get_node((fst, snd)))
            .collect()
    } else {
        let laccept = accept_idxs_lhs
            .into_iter()
            .cartesian_product(rhs_idxs.clone())
            .map(|(fst, snd)| cont.get_node((fst, snd)))
            .collect::<Vec<_>>()
            .into_iter();
        let r_accept = lhs_idxs
            .iter()
            .cartesian_product(accept_idxs_rhs)
            .map(|(fst, snd)| cont.get_node((*fst, snd)));
        laccept.chain(r_accept).collect()
    };

    let all_indeces: BTreeSet<usize> = lhs_idxs
        .iter()
        .cartesian_product(rhs_idxs)
        .map(|(lhs, rhs)| cont.get_node((*lhs, rhs)))
        .collect();

    assert!(!all_indeces.is_empty());

    ExplicitDFA {
        ent_id,
        edges: new_edges,
        accept_indexes,
        all_indeces,
    }
}

/// Unions the DFA by cartesian product
pub fn union<T, U, A>(lhs: &T, rhs: &U) -> impl DFA<A>
where
    A: Alphabet,
    A: Debug,
    T: DFA<A>,
    U: DFA<A>,
{
    let new_dfa = cartesian_product_internal(lhs, rhs, true);

    minimize(&new_dfa)
}

/// Compplement of the DFA
pub fn complement<T, A>(lhs: &T) -> impl DFA<A>
where
    A: Alphabet,
    A: Debug,
    T: DFA<A>,
{
    let all_indeces = BTreeSet::from_iter(lhs.all_indices().into_iter());
    let accept_indeces = BTreeSet::from_iter(lhs.accept_indices().into_iter());

    let new_accepts = all_indeces.difference(&accept_indeces).cloned().collect();

    ExplicitDFA {
        ent_id: lhs.entry(),
        all_indeces,
        accept_indexes: new_accepts,
        edges: BTreeSet::from_iter(lhs.dfa_edges().into_iter()),
    }
}

/// Checks if this DFA's language is empty
pub fn is_empty_language<A: Alphabet>(lhs: &impl DFA<A>) -> bool {
    let reached = get_reachable_idxs(lhs);
    // if the language is empty we shouldnt be able to reach any accept idxs
    !lhs.accept_indices()
        .into_iter()
        .any(|aidx| reached.contains(&aidx))
}

#[cfg(test)]
mod test {
    impl Alphabet for usize {}
    use std::collections::BTreeSet;

    use crate::solver::dfa_operations::{cartesian_product_internal, minimize, DFA};

    use super::{intersection, Alphabet, ExplicitDFA};

    #[test]
    fn test_null_intersection() {
        let lhs = ExplicitDFA::<usize> {
            ent_id: 0,
            edges: BTreeSet::from([(0, 10, 1), (1, 10, 1)]),
            accept_indexes: BTreeSet::from([0]),
            all_indeces: BTreeSet::from([0, 1]),
        };

        let rhs = ExplicitDFA::<usize> {
            ent_id: 0,
            edges: BTreeSet::from([(0, 10, 2), (2, 10, 2)]),
            accept_indexes: BTreeSet::from([0, 2]),
            all_indeces: BTreeSet::from([0, 2]),
        };

        let new_dfa = cartesian_product_internal(&lhs, &rhs, false);

        assert_eq!(new_dfa.accept_indices().len(), 2);
        assert_eq!(new_dfa.all_indices().len(), 4);

        // we shouldnt have incoming edges to accept nodes.
        for accept_idx in new_dfa.accept_indices() {
            assert!(new_dfa
                .dfa_edges()
                .into_iter()
                .find(|(_src, _, dst)| *dst == accept_idx)
                .is_none());
        }

        let min = minimize(&new_dfa);
        // just need an accept and then a reject
        assert_eq!(min.all_indices().len(), 2);
        assert_eq!(min.accept_indices().len(), 1);
    }

    #[test]
    fn test_empty_intersection() {
        let lhs = ExplicitDFA::<usize> {
            ent_id: 0,
            edges: BTreeSet::from([(0, 10, 1), (1, 10, 0)]),
            accept_indexes: BTreeSet::from([1]),
            all_indeces: BTreeSet::from([0, 1]),
        };

        let rhs = ExplicitDFA::<usize> {
            ent_id: 0,
            edges: BTreeSet::from([(0, 10, 1), (1, 10, 0)]),
            accept_indexes: BTreeSet::from([]),
            all_indeces: BTreeSet::from([0, 1]),
        };

        let res = intersection(&lhs, &rhs);
        assert_eq!(res.accept_indices().len(), 0);
        assert_eq!(res.all_indices().len(), 1);
        assert_eq!(res.dfa_edges().len(), 1);
    }

    #[test]
    fn test_simple_union() {
        let lhs = ExplicitDFA::<usize> {
            ent_id: 0,
            edges: BTreeSet::from([(0, 10, 1), (1, 10, 1)]),
            accept_indexes: BTreeSet::from([0]),
            all_indeces: BTreeSet::from([0, 1]),
        };

        let rhs = ExplicitDFA::<usize> {
            ent_id: 0,
            edges: BTreeSet::from([(0, 10, 2), (2, 10, 2)]),
            accept_indexes: BTreeSet::from([0, 2]),
            all_indeces: BTreeSet::from([0, 2]),
        };

        let new_dfa = cartesian_product_internal(&lhs, &rhs, true);

        assert_eq!(new_dfa.accept_indices().len(), 4);
        assert_eq!(new_dfa.all_indices().len(), 4);

        assert_eq!(new_dfa.dfa_edges().len(), 4);

        let minimal_dfa = minimize(&new_dfa);

        assert_eq!(minimal_dfa.accept_indices().len(), 1);
        assert_eq!(minimal_dfa.all_indices().len(), 1);
        assert_eq!(minimal_dfa.dfa_edges().len(), 1);

        let (src, _, dst) = minimal_dfa.dfa_edges()[0];
        assert_eq!(src, dst);
    }
}
