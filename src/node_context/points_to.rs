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
            Def::Load { var, address } => {
                if let Err(x) = new_ptr_state.handle_load(var, address, &self.rt_mem) {
                    warn!("{}", x.to_string());
                }
            }
            Def::Store { address, value } => {
                if let Err(x) = new_ptr_state.handle_store(address, value, &self.rt_mem) {
                    warn!("{}", x.to_string());
                }
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
}

impl PointsToContext {
    fn new(st: PointerState, stack_pointer: Variable) -> PointsToContext {
        PointsToContext {
            pointer_state: st,
            stack_pointer,
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
            offset: offset.try_to_offset().ok(),
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

        PointsToContext::new(new_ptr_state, self.stack_pointer.clone())
    }
}

impl PointsToMapping for PointsToContext {
    /// This method is conservative and only returns abstract objects for which we have an
    // TODO(ian): we should probably handle conflicting sizes
    fn points_to(
        &self,
        address: &cwe_checker_lib::intermediate_representation::Expression,
        sz: cwe_checker_lib::intermediate_representation::ByteSize,
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

    Ok(state_mapping
        .into_iter()
        .map(|(idx, ps)| {
            (
                idx,
                PointsToContext::new(ps, proj.stack_pointer_register.clone()),
            )
        })
        .collect())
}

#[cfg(test)]
mod test {
    use std::path::{Path, PathBuf};

    use cwe_checker_lib::{
        analysis::pointer_inference::Config,
        intermediate_representation::{ByteSize, Expression, Tid, Variable},
    };
    use petgraph::visit::IntoNodeReferences;

    use crate::{
        analysis::reaching_definitions::Definition,
        constraint_generation::{NodeContextMapping, PointsToMapping, RegisterMapping},
        constraints::VariableManager,
        inference_job::InferenceJob,
    };

    use super::run_analysis;

    fn test_data_dir<P: AsRef<Path>>(pth: P) -> String {
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push("test_data");
        d.push(pth);
        d.to_string_lossy().into_owned()
    }

    #[test]
    fn regression_globals_test() {
        let bin = InferenceJob::parse_binary(&test_data_dir("mooosl")).expect("Couldnt get binary");
        let proj = InferenceJob::parse_project(&test_data_dir("mooosl.json"), &bin)
            .expect("Couldnt get project");
        let grph = InferenceJob::graph_from_project(&proj);

        let rt_mem =
            InferenceJob::get_runtime_image(&proj, &bin).expect("coudlnt build memory image");
        let pointer_analysis = run_analysis(
            &proj,
            Config {
                allocation_symbols: vec![
                    "malloc".to_owned(),
                    "calloc".to_owned(),
                    "xmalloc".to_owned(),
                    "realloc".to_owned(),
                ],
                deallocation_symbols: vec!["free".to_owned()],
            },
            &grph,
            &rt_mem,
        )
        .expect("pointer analysis failed");

        let (target_idx, blk) = grph
            .node_references()
            .filter_map(|(idx, nd)| match nd {
                cwe_checker_lib::analysis::graph::Node::BlkStart(blk, prc) => {
                    if blk.tid.address == "00101522" {
                        Some((idx, blk))
                    } else {
                        None
                    }
                }
                cwe_checker_lib::analysis::graph::Node::BlkEnd(_, _) => None,
                cwe_checker_lib::analysis::graph::Node::CallReturn { .. } => None,
                cwe_checker_lib::analysis::graph::Node::CallSource { .. } => None,
            })
            .next()
            .expect("couldnt find tartget node");

        let point_to_res = pointer_analysis.get(&target_idx).expect("expected_context");

        let mut target_points_to = point_to_res.clone();
        let mut found = false;
        // fast forward the state to the target address
        for def in blk.term.defs.iter() {
            if !found {
                found = def.tid.address == "00101540";
            }

            if !found {
                target_points_to = point_to_res.apply_def(def);
            }
        }

        assert!(found);

        let mut fake_vman = VariableManager::new();
        let access = target_points_to.points_to(
            &Expression::Var(Variable {
                name: "RAX".to_owned(),
                size: ByteSize::new(8),
                is_temp: false,
            }),
            ByteSize::new(8),
        );
    }

    #[test]
    fn stack_allocated_list_heads() {
        let bin = InferenceJob::parse_binary(&test_data_dir("new_moosl_bin"))
            .expect("Couldnt get binary");
        let proj = InferenceJob::parse_project(&test_data_dir("new_moosl.json"), &bin)
            .expect("Couldnt get project");
        let grph = InferenceJob::graph_from_project(&proj);

        let rt_mem =
            InferenceJob::get_runtime_image(&proj, &bin).expect("coudlnt build memory image");
        let pointer_analysis = run_analysis(
            &proj,
            Config {
                allocation_symbols: vec![
                    "malloc".to_owned(),
                    "calloc".to_owned(),
                    "xmalloc".to_owned(),
                    "realloc".to_owned(),
                ],
                deallocation_symbols: vec!["free".to_owned()],
            },
            &grph,
            &rt_mem,
        )
        .expect("pointer analysis failed");

        let (target_idx, blk) = grph
            .node_references()
            .filter_map(|(idx, nd)| match nd {
                cwe_checker_lib::analysis::graph::Node::BlkStart(blk, prc) => {
                    if blk.tid.address == "00101526" {
                        Some((idx, blk))
                    } else {
                        None
                    }
                }
                cwe_checker_lib::analysis::graph::Node::BlkEnd(_, _) => None,
                cwe_checker_lib::analysis::graph::Node::CallReturn { .. } => None,
                cwe_checker_lib::analysis::graph::Node::CallSource { .. } => None,
            })
            .next()
            .expect("couldnt find tartget node");

        let point_to_res = pointer_analysis.get(&target_idx).expect("expected_context");

        let mut target_points_to = point_to_res.clone();
        let mut found = false;
        // fast forward the state to the target address
        for def in blk.term.defs.iter() {
            if !found {
                found = def.tid.address == "00101544";
            }

            if !found {
                target_points_to = point_to_res.apply_def(def);
            }
        }

        assert!(found);

        let access = target_points_to.points_to(
            &Expression::Var(Variable {
                name: "RAX".to_owned(),
                size: ByteSize::new(8),
                is_temp: false,
            }),
            ByteSize::new(8),
        );
    }
}
