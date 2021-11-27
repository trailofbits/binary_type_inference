use crate::analysis::stack_depth_analysis;
use crate::constraint_generation::{NodeContextMapping, PointsToMapping, TypeVariableAccess};
use crate::constraints::TypeVariable;
use anyhow::Result;
use cwe_checker_lib::abstract_domain::{
    AbstractIdentifier, DataDomain, IntervalDomain, TryToBitvec,
};
use cwe_checker_lib::analysis::graph::Graph;
use cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue;
use cwe_checker_lib::analysis::pointer_inference;
use cwe_checker_lib::intermediate_representation::{ByteSize, Def, Project, Variable};
use cwe_checker_lib::utils::binary::RuntimeMemoryImage;
use log::warn;
use petgraph::graph::NodeIndex;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

/// Wrpas a pointer state such that successor states can be generated.
#[derive(Clone)]
pub struct PointerState {
    /// The inner pointer inference state
    pub state: pointer_inference::State,
    rt_mem: Arc<RuntimeMemoryImage>,
}

impl NodeContextMapping for PointerState {
    fn apply_def(&self, term: &cwe_checker_lib::intermediate_representation::Term<Def>) -> Self {
        let mut new_ptr_state = self.state.clone();
        match &term.term {
            Def::Assign { var, value } => new_ptr_state.handle_register_assign(var, value),
            // TODO(ian): dont unwrap
            Def::Load { var, address } => new_ptr_state
                .handle_load(var, address, &self.rt_mem)
                .expect("Could not handle load"),
            Def::Store { address, value } => {
                new_ptr_state
                    .handle_store(address, value, &self.rt_mem)
                    .expect("Could not handle store");
            }
        };

        PointerState {
            state: new_ptr_state,
            rt_mem: self.rt_mem.clone(),
        }
    }
}

/// Holds a pointer_inference state for a node in order to mantain a type variable mapping for pointers.
#[derive(Clone)]
pub struct PointsToContext {
    pointer_state: PointerState,
    /// Stack pointer for the program, used to determine the stack offset
    pub stack_pointer: Variable,
    stack_depths: Arc<HashMap<AbstractIdentifier, i64>>,
}

impl PointsToContext {
    fn new(
        st: PointerState,
        stack_pointer: Variable,
        stack_depths: Arc<HashMap<AbstractIdentifier, i64>>,
    ) -> PointsToContext {
        PointsToContext {
            pointer_state: st,
            stack_pointer,
            stack_depths,
        }
    }
}

impl PointsToContext {
    /// Based on this comment in the AbstractObjectList:

    /// Right now this function is only sound if for each abstract object only one ID pointing to it exists.
    /// Violations of this will be detected and result in panics.
    /// Further investigation into the problem is needed
    /// to decide, how to correctly represent and handle cases,
    /// where more than one ID should point to the same object.
    ///

    /// We assume that abstract identifiers are unique.
    fn memory_access_into_tvar(
        &self,
        object_id: &AbstractIdentifier,
        offset: &IntervalDomain,
        sz: ByteSize,
    ) -> TypeVariableAccess {
        // TODO(ian): we may want to normalize this offset to the abstract object offset
        TypeVariableAccess {
            offset: offset.try_to_offset().ok().and_then(|off| {
                let mut curr_offset = off;
                if let Some(min_depth) = self.stack_depths.get(object_id) {
                    curr_offset += -min_depth;
                }

                if curr_offset.is_negative() {
                    warn!(
                        "Unhandled negative offset {:?} {} stack_id: {},",
                        object_id.to_string(),
                        curr_offset,
                        self.pointer_state.state.stack_id,
                    );
                    None
                } else {
                    Some(curr_offset)
                }
            }),
            ty_var: TypeVariable::new(
                object_id
                    .to_string()
                    .chars()
                    .filter(|c| !c.is_whitespace())
                    .collect(),
            ),
            sz,
        }
    }

    fn dom_val_to_tvars(
        &self,
        dom_val: &DataDomain<IntervalDomain>,
        sz: ByteSize,
    ) -> BTreeSet<TypeVariableAccess> {
        dom_val
            .get_relative_values()
            .iter()
            .map(|(a_id, offset)| self.memory_access_into_tvar(a_id, offset, sz))
            .collect()
    }
}

impl NodeContextMapping for PointsToContext {
    fn apply_def(
        &self,
        term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Def,
        >,
    ) -> Self {
        let new_ptr_state = self.pointer_state.apply_def(term);

        PointsToContext::new(
            new_ptr_state,
            self.stack_pointer.clone(),
            self.stack_depths.clone(),
        )
    }
}

impl PointsToMapping for PointsToContext {
    /// This method is conservative and only returns abstract objects for which we have an
    // TODO(ian): we should probably handle conflicting sizes
    fn points_to(
        &self,
        address: &cwe_checker_lib::intermediate_representation::Expression,
        sz: cwe_checker_lib::intermediate_representation::ByteSize,
        _vman: &mut crate::constraints::VariableManager,
    ) -> std::collections::BTreeSet<TypeVariableAccess> {
        let dom_val = self.pointer_state.state.eval(address);
        self.dom_val_to_tvars(&dom_val, sz)
    }
}

/// Runs analysis on the project to generate a [PointsToMapping]
pub fn run_analysis<'a>(
    proj: &'a Project,
    config: pointer_inference::Config,
    cfg: &'a Graph<'a>,
    rt_mem: &'a RuntimeMemoryImage,
) -> Result<HashMap<NodeIndex, PointsToContext>> {
    let pointer_res = pointer_inference::run(proj, rt_mem, cfg, config, false, false);

    let rt_mem = Arc::new(rt_mem.clone());

    let state_mapping: HashMap<NodeIndex, PointerState> = cfg
        .node_indices()
        .filter_map(|idx| {
            pointer_res.get_node_value(idx).and_then(|nv| match nv {
                NodeValue::CallFlowCombinator {
                    call_stub,
                    interprocedural_flow,
                } => (if interprocedural_flow.is_some() {
                    interprocedural_flow
                } else {
                    call_stub
                })
                .as_ref()
                .map(|v| {
                    (
                        idx,
                        PointerState {
                            rt_mem: rt_mem.clone(),
                            state: v.clone(),
                        },
                    )
                }),

                NodeValue::Value(v) => Some((
                    idx,
                    PointerState {
                        rt_mem: rt_mem.clone(),
                        state: v.clone(),
                    },
                )),
            })
        })
        .collect();

    let depth_context = stack_depth_analysis::Context::new(
        &state_mapping,
        cfg,
        proj.stack_pointer_register.clone(),
    );

    let stack_depths = Arc::new(depth_context.get_stack_depths());

    Ok(state_mapping
        .into_iter()
        .map(|(idx, ps)| {
            (
                idx,
                PointsToContext::new(
                    ps,
                    proj.stack_pointer_register.clone(),
                    stack_depths.clone(),
                ),
            )
        })
        .collect())
}
