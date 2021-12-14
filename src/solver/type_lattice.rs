use alga::general::{JoinSemilattice, Lattice, MeetSemilattice};
use cwe_checker_lib::abstract_domain::HasTop;
use itertools::Itertools;
use petgraph::{
    graph::NodeIndex,
    visit::{Dfs, GraphRef, IntoNeighbors, IntoNeighborsDirected, VisitMap, Visitable, Walker},
    Directed, EdgeDirection, Graph,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    rc::Rc,
};

trait NamedLattice<T: Lattice> {
    fn bot(&self) -> T;

    fn get_elem(&self, name: &str) -> Option<T>;

    fn top(&self) -> CustomLatticeElement;
}

struct EnumeratedNamedLattice {
    nds: HashMap<String, CustomLatticeElement>,
    bottom: CustomLatticeElement,
    top: CustomLatticeElement,
}

impl NamedLattice<CustomLatticeElement> for EnumeratedNamedLattice {
    fn get_elem(&self, name: &str) -> Option<CustomLatticeElement> {
        self.nds.get(name).cloned()
    }

    fn bot(&self) -> CustomLatticeElement {
        self.bottom.clone()
    }

    fn top(&self) -> CustomLatticeElement {
        self.top.clone()
    }
}

/// User input that defines a complete lattice.
#[derive(Debug, Deserialize, Serialize)]
struct LatticeDefinition {
    less_than_relations_between_handles: Vec<(String, String)>,
    top_handle: String,
    bottom_handle: String,
}

impl LatticeDefinition {
    fn get_lt_graph(&self) -> Graph<String, (), Directed> {
        let mut lt_grph = petgraph::Graph::new();
        let mut temp_node_holder = HashMap::new();
        for (x, y) in self
            .less_than_relations_between_handles
            .iter()
            .group_by(|(k, _)| k)
            .into_iter()
            .map(|(k, g)| (k, g.into_iter().map(|(k, x)| x).collect::<HashSet<_>>()))
        {
            let parent = *temp_node_holder
                .entry(x.to_owned())
                .or_insert_with(|| lt_grph.add_node(x.to_owned()));

            for greater in y.iter() {
                let greater = temp_node_holder
                    .entry(greater.to_string())
                    .or_insert_with(|| lt_grph.add_node(greater.to_string()));
                if !lt_grph.contains_edge(parent, *greater) {
                    lt_grph.add_edge(parent, *greater, ());
                }
            }
        }

        lt_grph
    }

    fn get_gt_graph(&self) -> Graph<String, (), Directed> {
        let mut lt = self.get_lt_graph();
        lt.reverse();
        lt
    }

    fn collect_reachable_nds<G: GraphRef + Visitable<NodeId = N, Map = VM>, N, VM>(
        g: G,
        star: N,
    ) -> HashSet<N>
    where
        N: Copy + PartialEq + Eq + Hash,
        VM: VisitMap<N>,
        G: IntoNeighbors,
    {
        Dfs::new(g, star).iter(&g).collect()
    }

    pub fn create_join_table(&self) -> HashMap<(String, String), String> {
        self.create_table(&self.get_lt_graph())
    }

    pub fn create_meet_table(&self) -> HashMap<(String, String), String> {
        self.create_table(&self.get_gt_graph())
    }

    // TODO(ian): I suspect this could be done around n^2 with a dynamic programming approach rather than just doing random node indeces.
    // The current iteration order demands a linear pass to determine the intersection

    // we can just pregenerate each gt or lt list then check the minimum of the intersection between each node's set but in the worst case this is still n^3.
    fn create_table(
        &self,
        graph: &Graph<String, (), Directed>,
    ) -> HashMap<(String, String), String> {
        let sort = petgraph::algo::toposort(graph, None)
            .expect("A lattice will allow for a topological sort")
            .into_iter()
            .enumerate()
            .map(|x| (x.1, x.0))
            .collect::<HashMap<_, _>>();

        let mut join_res: Vec<((NodeIndex, NodeIndex), NodeIndex)> = Vec::new();
        for (id1, id2) in graph
            .node_indices()
            .into_iter()
            .cartesian_product(graph.node_indices().into_iter())
        {
            let mut gt_set1 = Self::collect_reachable_nds(graph, id1);
            gt_set1.insert(id1);

            let mut gt_set2 = Self::collect_reachable_nds(graph, id2);
            gt_set2.insert(id2);
            let shared_reachable = gt_set1.intersection(&gt_set2).collect::<Vec<_>>();

            let lub = shared_reachable
                .into_iter()
                .min_by_key(|x| sort.get(x))
                .expect("every member should have a lub");
            join_res.push(((id1, id2), *lub));
        }

        join_res
            .into_iter()
            .map(|((k1, k2), v)| {
                (
                    (
                        graph.node_weight(k1).unwrap().to_string(),
                        graph.node_weight(k2).unwrap().to_string(),
                    ),
                    graph.node_weight(v).unwrap().to_string(),
                )
            })
            .collect()
    }

    fn create_reachable_sets(g: &Graph<String, (), Directed>) -> HashMap<String, HashSet<String>> {
        g.node_indices()
            .map(|x| (x, Self::collect_reachable_nds(&g, x)))
            .map(|(x, hset)| {
                (
                    g.node_weight(x).unwrap().to_string(),
                    hset.into_iter()
                        .map(|y| g.node_weight(y).unwrap().to_string())
                        .collect::<HashSet<_>>(),
                )
            })
            .collect()
    }

    fn create_less_than_sets(&self) -> HashMap<String, HashSet<String>> {
        let lt_graph = self.get_lt_graph();
        Self::create_reachable_sets(&lt_graph)
    }

    fn create_greater_than_sets(&self) -> HashMap<String, HashSet<String>> {
        let gt_graph = self.get_gt_graph();
        Self::create_reachable_sets(&gt_graph)
    }
    pub fn generate_lattice(&self) {
        let join = Rc::new(self.create_join_table());
        let meet = Rc::new(self.create_meet_table());
    }
}

/// Sets up a lattice as described by the user's definition
/// This is an ineffecient representation, block decomposition of lattices would be more effecient.
/// currently doesnt check any lattice laws, good luck
#[derive(Clone)]
struct CustomLatticeElement {
    elem: String,
    join_table: Rc<HashMap<(String, String), String>>,
    meet_table: Rc<HashMap<(String, String), String>>,
    /// Sets of nodes less than x
    orig_relation: HashMap<String, HashSet<String>>,
}

impl PartialEq for CustomLatticeElement {
    fn eq(&self, other: &Self) -> bool {
        self.elem == other.elem
    }
}

impl PartialOrd for CustomLatticeElement {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.elem == other.elem {
            return Some(std::cmp::Ordering::Equal);
        }

        let is_less = self
            .orig_relation
            .get(&self.elem)
            .unwrap()
            .contains(&other.elem);

        if is_less {
            return Some(std::cmp::Ordering::Less);
        }

        let is_more = self
            .orig_relation
            .get(&other.elem)
            .unwrap()
            .contains(&self.elem);

        if is_more {
            return Some(std::cmp::Ordering::Greater);
        }

        None
    }
}

impl Lattice for CustomLatticeElement {}

impl JoinSemilattice for CustomLatticeElement {
    fn join(&self, other: &Self) -> Self {
        self.join_table
            .get(&(self.elem.to_owned(), other.elem.to_owned()))
            .map(|x| CustomLatticeElement {
                elem: x.clone(),
                join_table: self.join_table.clone(),
                meet_table: self.meet_table.clone(),
                orig_relation: self.orig_relation.clone(),
            })
            .expect("All relations should be defined in table")
    }
}

impl MeetSemilattice for CustomLatticeElement {
    fn meet(&self, other: &Self) -> Self {
        self.meet_table
            .get(&(self.elem.to_owned(), other.elem.to_owned()))
            .map(|x| CustomLatticeElement {
                elem: x.clone(),
                join_table: self.join_table.clone(),
                meet_table: self.meet_table.clone(),
                orig_relation: self.orig_relation.clone(),
            })
            .expect("All relations should be defined in table")
    }
}
