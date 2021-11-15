use crate::constraint_generation::{PointsToMapping, TypeVariableAccess};
use crate::constraints::{ConstraintSet, DerivedTypeVar, SubtypeConstraint, TypeVariable};
use anyhow::Result;
use cwe_checker_lib::abstract_domain::{AbstractIdentifier, IntervalDomain, TryToBitvec};
use cwe_checker_lib::analysis::graph::Graph;
use cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue;
use cwe_checker_lib::analysis::pointer_inference;
use cwe_checker_lib::analysis::pointer_inference::PointerInference;
use cwe_checker_lib::analysis::{forward_interprocedural_fixpoint, graph};
use cwe_checker_lib::intermediate_representation::Project;
use cwe_checker_lib::utils::binary::RuntimeMemoryImage;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use std::fmt::Pointer;
use std::rc::Rc;

// Each node context holds a reference to
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
    ) -> TypeVariableAccess {
        // TODO(ian): Is this sign always right
        // TODO(ian): we may want to normalize this offset to the abstract object offset
        TypeVariableAccess {
            offset: offset.try_to_offset().ok(),
            ty_var: TypeVariable::new(object_id.to_string()),
        }
    }
}

impl PointsToMapping for PointsToContext {
    /// This method is conservative and only returns abstract objects for which we have an
    // TODO(ian): we should probably handle conflicting sizes
    fn points_to(
        &self,
        address: &cwe_checker_lib::intermediate_representation::Expression,
        _sz: cwe_checker_lib::intermediate_representation::ByteSize,
        _vman: &mut crate::constraints::VariableManager,
    ) -> std::collections::BTreeSet<TypeVariableAccess> {
        let dom_val = self.pointer_state.eval(address);
        dom_val
            .get_relative_values()
            .into_iter()
            .map(|(a_id, offset)| self.memory_access_into_tvar(a_id, offset))
            .collect()
    }
}

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
                NodeValue::CallFlowCombinator { .. } => None,
                NodeValue::Value(v) => Some((idx.clone(), PointsToContext::new(v.clone()))),
            })
        })
        .collect())
}
