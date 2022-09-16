use alga::general::{JoinSemilattice, Lattice, MeetSemilattice};
use itertools::Itertools;
use petgraph::{
    graph::NodeIndex,
    visit::{Dfs, GraphRef, IntoNeighbors, VisitMap, Visitable, Walker},
    Directed, Graph,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    rc::Rc,
};

/// A named lattice elment can be cloned and also has a string name.
pub trait NamedLatticeElement: Lattice + Clone {
    /// The name of this lattice element.
    fn get_name(&self) -> &str;

    /// Check wether this is the top element.
    fn is_top(&self) -> bool;

    /// Check wether this is the bottom element.
    fn is_bot(&self) -> bool;
}

/// A named lattice has a top element, bottom element, and can lookup lattice elements by name.
pub trait NamedLattice<T: NamedLatticeElement> {
    /// The bottom lattice element.
    fn bot(&self) -> T;

    /// Finds the element with the name name, if it exists.
    fn get_elem(&self, name: &str) -> Option<T>;

    /// The top lattice element.
    fn top(&self) -> T;
}

/// A named lattice that is created by user input enumerating the less than relations that are not
/// transitive.
pub struct EnumeratedNamedLattice {
    nds: HashMap<String, CustomLatticeElement>,
    bottom: CustomLatticeElement,
    top: CustomLatticeElement,
}

impl EnumeratedNamedLattice {
    /// Gets a map from the string representing a node to the lattice element, equipped with lattice operations.
    pub fn get_nds(&self) -> &HashMap<String, CustomLatticeElement> {
        &self.nds
    }
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
pub struct LatticeDefinition {
    less_than_relations_between_handles: Vec<(String, String)>,
    top_handle: String,
    bottom_handle: String,
    weakest_integral_type: String,
}

impl LatticeDefinition {
    /// Merge two [LatticeDefinitions]'
    pub fn merge_with_other(mut self, def: LatticeDefinition) -> anyhow::Result<LatticeDefinition> {
        self.less_than_relations_between_handles
            .extend(def.less_than_relations_between_handles.into_iter());
        Ok(self)
    }

    /// Creates a new user defined lattice from element names.
    pub fn new(
        less_than_relations_between_handles: Vec<(String, String)>,
        top_handle: String,
        bottom_handle: String,
        weakest_integral_type: String,
    ) -> LatticeDefinition {
        LatticeDefinition {
            less_than_relations_between_handles,
            top_handle,
            bottom_handle,
            weakest_integral_type,
        }
    }

    /// Gets the greatest (weakest) type name that is an integer.
    pub fn get_weakest_integral_type(&self) -> &str {
        &self.weakest_integral_type
    }

    fn get_lt_graph(&self) -> Graph<String, (), Directed> {
        let mut lt_grph = petgraph::Graph::new();
        let mut temp_node_holder = HashMap::new();
        for (x, y) in self
            .less_than_relations_between_handles
            .iter()
            .fold(
                HashMap::<String, HashSet<String>>::new(),
                |mut total, (x, y)| {
                    total.entry(x.clone()).or_default().insert(y.clone());
                    total
                },
            )
            .into_iter()
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

    /// Creates a join tables where each pair of elements is mapped to their join.
    pub fn create_join_table(&self) -> HashMap<(String, String), String> {
        self.create_table(&self.get_lt_graph())
    }

    /// Creates a precomputed table of the meets for each element.
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
            let shared_reachable = gt_set1.intersection(&gt_set2);

            let lub = shared_reachable
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

    /// From a user definition generates a named lattice that has joins, meets, and a lookup table for the less than relation.
    pub fn generate_lattice(&self) -> EnumeratedNamedLattice {
        let join = Rc::new(self.create_join_table());
        let meet = Rc::new(self.create_meet_table());
        let lt_set = Rc::new(self.create_less_than_sets());

        let top = CustomLatticeElement {
            elem: self.top_handle.clone(),
            bot: self.bottom_handle.clone(),
            top: self.top_handle.clone(),
            join_table: join,
            meet_table: meet,
            orig_relation: lt_set,
        };

        let bot = CustomLatticeElement {
            elem: self.bottom_handle.clone(),
            ..top.clone()
        };

        let nds: HashMap<String, CustomLatticeElement> = self
            .less_than_relations_between_handles
            .iter()
            .flat_map(|x| vec![&x.0, &x.1].into_iter())
            .map(|elem| {
                (
                    elem.clone(),
                    CustomLatticeElement {
                        elem: elem.clone(),
                        ..top.clone()
                    },
                )
            })
            .chain(
                vec![
                    (top.elem.clone(), top.clone()),
                    (bot.elem.clone(), bot.clone()),
                ]
                .into_iter(),
            )
            .collect();

        EnumeratedNamedLattice {
            nds,
            top,
            bottom: bot,
        }
    }
}

/// Sets up a lattice as described by the user's definition
/// This is an ineffecient representation, block decomposition of lattices would be more effecient.
/// currently doesnt check any lattice laws, good luck
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CustomLatticeElement {
    top: String,
    bot: String,
    elem: String,
    join_table: Rc<HashMap<(String, String), String>>,
    meet_table: Rc<HashMap<(String, String), String>>,
    /// Sets of nodes less than x
    orig_relation: Rc<HashMap<String, HashSet<String>>>,
}

impl NamedLatticeElement for CustomLatticeElement {
    fn get_name(&self) -> &str {
        &self.elem
    }

    fn is_top(&self) -> bool {
        self.top == self.elem
    }

    fn is_bot(&self) -> bool {
        self.bot == self.elem
    }
}

impl Display for CustomLatticeElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.elem)
    }
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
                top: self.top.clone(),
                bot: self.bot.clone(),
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
                top: self.top.clone(),
                bot: self.bot.clone(),
            })
            .expect("All relations should be defined in table")
    }
}
