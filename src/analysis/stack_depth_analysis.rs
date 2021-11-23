/*
use cwe_checker_lib::{
    abstract_domain::AbstractIdentifier,
    analysis::{graph::Graph, pointer_inference::State},
};
use petgraph::csr::NodeIndex;
use std::collections::HashMap;

struct Context<'a> {
    node_contexts: HashMap<NodeIndex, State>,
    graph: &'a Graph<'a>,
}

impl Context {
    pub fn get_stack_depths(&self) -> HashMap<AbstractIdentifier> {
        for nd_idx in self.graph.node_indices() {
            let nd_ctx = self.node_contexts.get(nd_idx);
            if let Some(nd_ctx) = nd_ctx {
                match self.graph[nd_idx] {
                    state
                }
            }
        }
    }
}*/
