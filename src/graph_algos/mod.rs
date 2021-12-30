use std::{hash::Hash, iter::FromIterator};

use indexmap::IndexSet;
use petgraph::{
    visit::{EdgeRef, IntoEdgesDirected, NodeCount},
};
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
