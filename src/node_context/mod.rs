use std::collections::HashMap;

use cwe_checker_lib::{
    analysis::{graph::Graph, pointer_inference::Config},
    intermediate_representation::Project,
    utils::binary::RuntimeMemoryImage,
};
use petgraph::graph::NodeIndex;

use crate::{
    constraint_generation::{NodeContext, PointsToMapping, RegisterMapping, SubprocedureLocators},
    constraints::TypeVariable,
};

/// Wraps the cwe_checker points to analysis to generate type variables related to stores and loads based on the [cwe_checker_lib::abstract_domain::AbstractIdentifier].
pub mod points_to;

/// Maps register accesses to type variables and constraints using a reaching definitions analysis.
pub mod register_map;

/// A subprocedure locator that evaluates arguments and return values to type variables.
pub mod subproc_loc;

use anyhow::Result;
use std::iter::Iterator;

use self::{
    points_to::PointsToContext, register_map::RegisterContext, subproc_loc::ProcedureContext,
};

/// Joins mappings from [NodeIndex] to each analysis result into a singular map of [NodeContext].  
pub fn make_node_contexts<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators>(
    mut register_contexts: HashMap<NodeIndex, R>,
    mut points_to_contexts: HashMap<NodeIndex, P>,
    mut subproc_contexts: HashMap<NodeIndex, S>,
    nodes: impl Iterator<Item = NodeIndex>,
    weakest_integral_type: TypeVariable,
) -> HashMap<NodeIndex, NodeContext<R, P, S>> {
    nodes
        .filter_map(|idx| {
            let r = register_contexts.remove(&idx);
            let p = points_to_contexts.remove(&idx);
            let s = subproc_contexts.remove(&idx);

            match (r, p, s) {
                (Some(r), Some(p), Some(s)) => Some((
                    idx,
                    NodeContext::new(r, p, s, weakest_integral_type.clone()),
                )),
                _ => None,
            }
        })
        .collect()
}

/// Creates a default context with the default analyses [register_map], [points_to], and [subproc_loc]
pub fn create_default_context(
    proj: &Project,
    graph: &Graph,
    config: Config,
    rt_mem: &RuntimeMemoryImage,
    weakest_integral_type: TypeVariable,
) -> Result<HashMap<NodeIndex, NodeContext<RegisterContext, PointsToContext, ProcedureContext>>> {
    let reg_context = register_map::run_analysis(proj, graph);

    let points_to_context = points_to::run_analysis(proj, config, graph, rt_mem)?;

    let proc_handler = ProcedureContext {
        stack_pointer: proj.stack_pointer_register.clone(),
    };
    let proc_context: HashMap<NodeIndex, ProcedureContext> = graph
        .node_indices()
        .map(|idx| (idx, proc_handler.clone()))
        .collect();

    Ok(make_node_contexts(
        reg_context,
        points_to_context,
        proc_context,
        graph.node_indices(),
        weakest_integral_type,
    ))
}
