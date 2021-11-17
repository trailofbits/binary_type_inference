use crate::constraint_generation::{PointsToMapping, TypeVariableAccess};
use crate::constraints::TypeVariable;
use anyhow::Result;
use cwe_checker_lib::abstract_domain::{
    AbstractIdentifier, DataDomain, IntervalDomain, TryToBitvec,
};
use cwe_checker_lib::analysis::graph::Graph;
use cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue;
use cwe_checker_lib::analysis::pointer_inference;
use cwe_checker_lib::intermediate_representation::{ByteSize, Project};
use cwe_checker_lib::utils::binary::RuntimeMemoryImage;
use log::warn;
use petgraph::graph::NodeIndex;
use std::collections::{BTreeSet, HashMap};

/// Holds a pointer_inference state for a node in order to mantain a type variable mapping for pointers.
pub struct PointsToContext {
    pointer_state: pointer_inference::State,
}

impl PointsToContext {
    fn new(st: pointer_inference::State) -> PointsToContext {
        PointsToContext { pointer_state: st }
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
        // TODO(ian): So retypd doesnt handle negative offsets, how do we handle this
        // TODO(ian): we may want to normalize this offset to the abstract object offset
        TypeVariableAccess {
            offset: offset.try_to_offset().ok().and_then(|off| {
                if off.is_negative() {
                    warn!(
                        "Unhandled negative offset {:?} {}",
                        object_id.to_string(),
                        off
                    );
                    None
                } else {
                    Some(off)
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

impl PointsToMapping for PointsToContext {
    /// This method is conservative and only returns abstract objects for which we have an
    // TODO(ian): we should probably handle conflicting sizes
    fn points_to(
        &self,
        address: &cwe_checker_lib::intermediate_representation::Expression,
        sz: cwe_checker_lib::intermediate_representation::ByteSize,
        _vman: &mut crate::constraints::VariableManager,
    ) -> std::collections::BTreeSet<TypeVariableAccess> {
        let dom_val = self.pointer_state.eval(address);
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

    Ok(cfg
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
                .map(|v| (idx, PointsToContext::new(v.clone()))),

                NodeValue::Value(v) => Some((idx, PointsToContext::new(v.clone()))),
            })
        })
        .collect())
}
