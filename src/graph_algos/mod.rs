use std::{hash::Hash, iter::FromIterator};

use indexmap::IndexSet;
use petgraph::visit::{Data, EdgeRef, IntoEdgesDirected, NodeCount};

pub mod mapping_graph;

/// All simple paths that tracks edge paths instead of node paths
pub fn all_simple_paths<TargetColl, G>(
    graph: G,
    from: G::NodeId,
    to: G::NodeId,
) -> impl Iterator<Item = TargetColl>
where
    G: NodeCount,
    G: IntoEdgesDirected,
    G::EdgeId: Eq + Hash,
    TargetColl: FromIterator<G::EdgeId>,
{
    let mut visited: IndexSet<G::EdgeId> = IndexSet::from_iter(None);
    let mut stack = vec![graph.edges_directed(from, petgraph::EdgeDirection::Outgoing)];
    std::iter::from_fn(move || {
        while let Some(children) = stack.last_mut() {
            if let Some(child) = children.next() {
                if child.target() == to {
                    let path = visited
                        .iter()
                        .cloned()
                        .chain(Some(child.id()))
                        .collect::<TargetColl>();
                    return Some(path);
                } else if !visited.contains(&child.id()) {
                    visited.insert(child.id());
                    stack.push(
                        graph.edges_directed(child.target(), petgraph::EdgeDirection::Outgoing),
                    );
                }
            } else {
                stack.pop();
                visited.pop();
            }
        }
        None
    })
}

/// DFS for exploring nodes but provides a path to each node, useful for collecting
/// DFA strings.
pub fn explore_paths<G>(
    graph: G,
    start: G::NodeId,
) -> impl Iterator<Item = (im_rc::Vector<G::EdgeId>, G::NodeId)>
where
    G: NodeCount,
    G::NodeId: Eq + Hash,
    G: IntoEdgesDirected,
{
    let mut stack: Vec<(im_rc::Vector<G::EdgeId>, G::NodeId)> = vec![(im_rc::Vector::new(), start)];
    let mut visited: IndexSet<G::NodeId> = IndexSet::from_iter(None);
    std::iter::from_fn(move || {
        while let Some((reaching_path, nxt_node)) = stack.pop() {
            if visited.contains(&nxt_node) {
                continue;
            }

            visited.insert(nxt_node);

            for e in graph.edges_directed(nxt_node, petgraph::EdgeDirection::Outgoing) {
                if !visited.contains(&e.target()) {
                    let mut new_pth = reaching_path.clone();
                    new_pth.push_back(e.id());
                    stack.push((new_pth, e.target()));
                }
            }
            return Some((reaching_path, nxt_node));
        }
        None
    })
}

/// Follows a path to a NodeId if the node is reachable
pub fn find_node<'a, G>(
    graph: G,
    start: G::NodeId,
    path: impl Iterator<Item = &'a G::EdgeWeight>,
) -> Option<G::NodeId>
where
    G: Data,
    G::EdgeWeight: 'a,
    G::EdgeWeight: Hash + Eq,
    G: IntoEdgesDirected,
{
    let mut curr_node = start;
    let mut iter = path.into_iter();

    while let Some(take_edge) = iter.next() {
        let mut edges = graph.edges_directed(curr_node, petgraph::EdgeDirection::Outgoing);

        if let Some(e) = edges.find(|e| e.weight() == take_edge) {
            curr_node = e.target();
        } else {
            return None;
        }
    }

    Some(curr_node)
}
