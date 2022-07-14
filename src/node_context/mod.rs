use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap},
    rc::Rc,
};

use cwe_checker_lib::{
    analysis::pointer_inference::Config,
    intermediate_representation::{Program, Tid},
    AnalysisResults,
};
use log::info;
use petgraph::graph::NodeIndex;

use crate::{
    constraint_generation::{
        ConstantResolver, NodeContext, NodeContextMapping, PointsToMapping, RegisterMapping,
        SubprocedureLocators,
    },
    constraints::{DerivedTypeVar, TypeVariable},
    util::FileDebugLogger,
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
pub fn make_node_contexts<
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    C: ConstantResolver,
>(
    mut register_contexts: HashMap<NodeIndex, R>,
    mut points_to_contexts: HashMap<NodeIndex, P>,
    mut subproc_contexts: HashMap<NodeIndex, S>,
    mut constant_contexts: HashMap<NodeIndex, C>,
    nodes: impl Iterator<Item = NodeIndex>,
    weakest_integral_type: TypeVariable,
) -> HashMap<NodeIndex, NodeContext<R, P, S, C>> {
    nodes
        .filter_map(|idx| {
            let r = register_contexts.remove(&idx);
            let p = points_to_contexts.remove(&idx);
            let s = subproc_contexts.remove(&idx);
            let c = constant_contexts.remove(&idx);
            match (r, p, s, c) {
                (Some(r), Some(p), Some(s), Some(c)) => Some((
                    idx,
                    NodeContext::new(r, p, s, c, weakest_integral_type.clone()),
                )),
                _ => None,
            }
        })
        .collect()
}

#[derive(Debug, Clone)]
/// A [ConstantResolver] implementation that uses ghidra
/// to map some known addresses to global variable terms.
pub struct GhidraConstantResolver {
    global_map: Rc<BTreeMap<u64, Tid>>,
}

impl<T> From<T> for GhidraConstantResolver
where
    T: Borrow<Program>,
{
    fn from(prog: T) -> Self {
        let p = prog.borrow();

        let mp = p
            .global_variables
            .iter()
            .map(|(b, term)| (*b, term.tid.clone()))
            .collect();

        GhidraConstantResolver {
            global_map: Rc::new(mp),
        }
    }
}

impl NodeContextMapping for GhidraConstantResolver {
    fn apply_def(
        &self,
        _term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Def,
        >,
    ) -> Self {
        self.clone()
    }

    fn apply_return_node(
        &self,
        call_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
        return_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
    ) -> Self {
        self.clone()
    }
}

impl ConstantResolver for GhidraConstantResolver {
    fn maybe_resolve_constant_to_variable(
        &self,
        target: &cwe_checker_lib::intermediate_representation::Bitvector,
    ) -> Option<DerivedTypeVar> {
        target
            .try_to_u64()
            .ok()
            .and_then(|tgt| {
                self.global_map
                    .get(&tgt)
                    .map(|t| TypeVariable::new_global(t.get_str_repr().to_owned()))
            })
            .map(|vr| DerivedTypeVar::new(vr))
    }
}

/// Creates a default context with the default analyses [register_map], [points_to], and [subproc_loc]
pub fn create_default_context<'a>(
    proj: &'a AnalysisResults<'a>,
    config: Config,
    weakest_integral_type: TypeVariable,
    debug_dir: FileDebugLogger,
) -> Result<
    HashMap<
        NodeIndex,
        NodeContext<RegisterContext, PointsToContext, ProcedureContext, GhidraConstantResolver>,
    >,
> {
    let reg_context = register_map::run_analysis(proj.project, proj.control_flow_graph);

    for nd_idx in proj.control_flow_graph.node_indices() {
        let nd = &proj.control_flow_graph[nd_idx];
        if let cwe_checker_lib::analysis::graph::Node::BlkStart(blk_term, sub_term) = nd {
            if sub_term.term.blocks[0].tid == blk_term.tid {
                // entry block
                if let Some(defs) = reg_context.get(&nd_idx) {
                    debug_dir.log_to_fname(
                        &format!("reg_defs_entry_{}", sub_term.tid.get_str_repr()),
                        &|| defs,
                    )?;
                }
            }
        }
    }

    let points_to_context = points_to::run_analysis(proj, config)?;

    let proc_handler = ProcedureContext {
        stack_pointer: proj.project.stack_pointer_register.clone(),
    };
    let proc_context: HashMap<NodeIndex, ProcedureContext> = proj
        .control_flow_graph
        .node_indices()
        .map(|idx| (idx, proc_handler.clone()))
        .collect();

    let const_context = GhidraConstantResolver::from(&proj.project.program.term);

    Ok(make_node_contexts(
        reg_context,
        points_to_context,
        proc_context,
        proj.control_flow_graph
            .node_indices()
            .map(|idx| (idx, const_context.clone()))
            .collect(),
        proj.control_flow_graph.node_indices(),
        weakest_integral_type,
    ))
}
