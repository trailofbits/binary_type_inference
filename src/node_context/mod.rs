use std::collections::HashMap;

use cwe_checker_lib::{
    analysis::pointer_inference::Config, intermediate_representation::Project,
    utils::binary::RuntimeMemoryImage,
};
use petgraph::graph::NodeIndex;

use crate::constraint_generation::{
    NodeContext, PointsToMapping, RegisterMapping, SubprocedureLocators,
};

pub mod points_to;
pub mod register_map;
pub mod subproc_loc;
use anyhow::Result;
use std::iter::Iterator;

use self::{
    points_to::PointsToContext, register_map::RegisterContext, subproc_loc::ProcedureContext,
};

pub fn make_node_contexts<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators>(
    mut register_contexts: HashMap<NodeIndex, R>,
    mut points_to_contexts: HashMap<NodeIndex, P>,
    mut subproc_contexts: HashMap<NodeIndex, S>,
    nodes: impl Iterator<Item = NodeIndex>,
) -> HashMap<NodeIndex, NodeContext<R, P, S>> {
    nodes
        .filter_map(|idx| {
            let r = register_contexts.remove(&idx);
            let p = points_to_contexts.remove(&idx);
            let s = subproc_contexts.remove(&idx);

            match (r, p, s) {
                (Some(r), Some(p), Some(s)) => Some((idx, NodeContext::new(r, p, s))),
                _ => None,
            }
        })
        .collect()
}

pub fn create_default_context(
    proj: &Project,
    config: Config,
    rt_mem: &RuntimeMemoryImage,
) -> Result<HashMap<NodeIndex, NodeContext<RegisterContext, PointsToContext, ProcedureContext>>> {
    let extern_subs = proj.program.term.extern_symbols.keys().cloned().collect();
    let mut graph = cwe_checker_lib::analysis::graph::get_program_cfg(&proj.program, extern_subs);

    let reg_context = register_map::run_analysis(proj, &graph);

    let points_to_context = points_to::run_analysis(proj, config, &graph, rt_mem)?;

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
    ))
}
