use crate::{constraint_generation, node_context::points_to::PointerState};
use cwe_checker_lib::{
    abstract_domain::{AbstractIdentifier, TryToBitvec},
    analysis::{
        graph::{Graph, Node},
        pointer_inference::State,
    },
    intermediate_representation::{Blk, Term, Variable},
};
use petgraph::graph::NodeIndex;
use std::collections::HashMap;

pub struct Context<'a> {
    node_contexts: &'a HashMap<NodeIndex, PointerState>,
    graph: &'a Graph<'a>,
    stack_pointer: Variable,
}

fn merge_into(
    into_map: &mut HashMap<AbstractIdentifier, i64>,
    from_map: &HashMap<AbstractIdentifier, i64>,
) {
    for (k, v) in from_map.iter() {
        into_map.insert(
            k.clone(),
            into_map
                .get(k)
                .map(|other| if other < v { other } else { v })
                .unwrap_or(v)
                .clone(),
        );
    }
}

impl<'a> Context<'a> {
    pub fn new(
        node_contexts: &'a HashMap<NodeIndex, PointerState>,
        graph: &'a Graph<'a>,
        stack_pointer: Variable,
    ) -> Context<'a> {
        Context {
            node_contexts,
            graph,
            stack_pointer,
        }
    }

    fn get_current_stack_depth(&self, state: &State) -> Option<(AbstractIdentifier, i64)> {
        if let Some((stack_id, sp_off)) = state
            .get_register(&self.stack_pointer)
            .get_if_unique_target()
        {
            sp_off
                .try_to_offset()
                .ok()
                .map(|off| (stack_id.clone(), off))
        } else {
            None
        }
    }

    fn compute_min_depth_for_blk(
        &self,
        start_state: PointerState,
        blk: &Term<Blk>,
    ) -> HashMap<AbstractIdentifier, i64> {
        constraint_generation::fold_over_definition_states(
            start_state,
            blk,
            HashMap::new(),
            &mut |_def, ctxt, mut inner_state| {
                let st: HashMap<AbstractIdentifier, i64> = self
                    .get_current_stack_depth(&ctxt.state)
                    .into_iter()
                    .collect();

                merge_into(&mut inner_state, &st);
                inner_state
            },
        )
    }

    pub fn get_stack_depths(&self) -> HashMap<AbstractIdentifier, i64> {
        let mut min_stack_depth: HashMap<AbstractIdentifier, i64> = HashMap::new();
        for nd_idx in self.graph.node_indices() {
            let nd_ctx = self.node_contexts.get(&nd_idx);
            if let Some(nd_ctx) = nd_ctx {
                match self.graph[nd_idx] {
                    Node::BlkStart(blk, _sub) => {
                        let new_offsets = self.compute_min_depth_for_blk(nd_ctx.clone(), blk);
                        merge_into(&mut min_stack_depth, &new_offsets);
                    }
                    _ => (),
                }
            }
        }

        min_stack_depth
    }
}
