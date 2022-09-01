use crate::constraint_generation::{
    ConstantResolver, NodeContextMapping, PointsToMapping, TypeVariableAccess,
};
use crate::constraints::{DerivedTypeVar, TypeVariable};

use anyhow::Result;
use cwe_checker_lib::abstract_domain::{
    AbstractIdentifier, DataDomain, IntervalDomain, TryToBitvec,
};

use cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue;
use cwe_checker_lib::analysis::pointer_inference::{self, Config};
use cwe_checker_lib::intermediate_representation::{ByteSize, Def, Expression, Variable};
use cwe_checker_lib::AnalysisResults;

use cwe_checker_lib::utils::binary::RuntimeMemoryImage;
use log::warn;
use petgraph::graph::NodeIndex;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

lazy_static! {
    /// The default set of allocation symbols an deallocation symbols
    pub static ref DEFAULT_PTR_CONFIG: Config = {
        Config {
            allocation_symbols: vec![
                "malloc".to_owned(),
                "calloc".to_owned(),
                "xmalloc".to_owned(),
                "realloc".to_owned(),
            ],
            deallocation_symbols: vec!["free".to_owned()],
        }
    };
}

/// Wraps a pointer state such that successor states can be generated.
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

    fn apply_return_node(
        &self,
        _call_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
        _return_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
    ) -> Self {
        // TODO(Ian): This is only ok because "generally" pointer returns arent a thing. Revisit this. What we need to do to fast forward the pointer state
        // is call the update_return method on the pointer inference context but that is a private structure in cwe checker. We could expose it and store the context as
        // an Rc in every node but that isnt ideal.
        self.clone()
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
    pub fn type_variable_from_abstract_id(aid: &AbstractIdentifier) -> TypeVariable {
        TypeVariable::new(
            aid.to_string()
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect(),
        )
    }

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
            ty_var: Self::type_variable_from_abstract_id(object_id),

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

    fn apply_return_node(
        &self,
        call_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
        return_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
    ) -> Self {
        PointsToContext {
            pointer_state: self.pointer_state.apply_return_node(call_term, return_term),
            stack_pointer: self.stack_pointer.clone(),
        }
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

    /// Attempts to resolve a pointer expression to a variable
    fn get_pointer_variable(
        &self,
        address: &Expression,
        constant_resolver: &impl ConstantResolver,
    ) -> Option<DerivedTypeVar> {
        if let Some(absolute_ptr) = self
            .pointer_state
            .state
            .eval(address)
            .get_if_absolute_value()
        {
            if let Ok(bv) = absolute_ptr.try_to_bitvec() {
                return constant_resolver.maybe_resolve_constant_to_variable(&bv);
            }
        }
        None
    }
}

/// Runs analysis on the project to generate a [PointsToMapping]
pub fn run_analysis<'a>(
    analysis_results: &'a AnalysisResults<'a>,
    config: pointer_inference::Config,
) -> Result<HashMap<NodeIndex, PointsToContext>> {
    let pointer_res = pointer_inference::run(analysis_results, config, false, false);

    let rt_mem = Arc::new(analysis_results.runtime_memory_image.clone());

    let state_mapping: HashMap<NodeIndex, PointerState> = analysis_results
        .control_flow_graph
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
                PointsToContext::new(ps, analysis_results.project.stack_pointer_register.clone()),
            )
        })
        .collect())
}

#[cfg(test)]
mod test {

    use std::path::{Path, PathBuf};

    use cwe_checker_lib::{
        abstract_domain::{AbstractDomain, TryToBitvec, TryToInterval},
        analysis::graph::{Graph, Node},
        intermediate_representation::{
            BinOpType, Bitvector, Blk, ByteSize, Expression, Term, Tid, Variable,
        },
        utils::binary::RuntimeMemoryImage,
        AnalysisResults,
    };
    use petgraph::{data, stable_graph::NodeIndex};

    use crate::{
        constraint_generation::NodeContextMapping, inference_job::InferenceJob,
        node_context::points_to::PointsToContext,
    };

    use super::{run_analysis, DEFAULT_PTR_CONFIG};

    fn test_data_dir<P: AsRef<Path>>(pth: P) -> String {
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push("test_data");
        d.push(pth);
        d.to_string_lossy().into_owned()
    }

    fn find_ndidx_for_block<'a>(addr: &str, cfg: &Graph<'a>) -> Option<(NodeIndex, Node<'a>)> {
        for ndidx in cfg.node_indices() {
            let nd = cfg[ndidx];
            if nd.get_block().tid.address == addr {
                return Some((ndidx, nd));
            }
        }

        None
    }

    fn fast_forward_pointer_state_until_address_term(
        mut ctx: PointsToContext,
        target_tid: &str,
        blk: &Term<Blk>,
    ) -> PointsToContext {
        for d in &blk.term.defs {
            if &d.tid.address == target_tid {
                return ctx;
            }
            println!("Applying def with tid: {}", d.tid);
            println!("{:#?}", d);
            ctx = ctx.apply_def(d);
        }

        ctx
    }

    fn check_target_stack_value(target_ctx: &PointsToContext, rt_mem: &RuntimeMemoryImage) {
        let rbp = Variable {
            name: "RBP".to_owned(),
            size: ByteSize::from(8),
            is_temp: false,
        };

        let stored_value = target_ctx
            .pointer_state
            .state
            .load_value(
                &Expression::BinOp {
                    op: BinOpType::IntAdd,
                    lhs: Box::new(Expression::Var(rbp)),
                    rhs: Box::new(Expression::Const(Bitvector::from_i64(-16))),
                },
                ByteSize::from(8),
                rt_mem,
            )
            .expect("should be able to retrieve value stored in local_18");

        let (aid, offset) = stored_value.get_if_unique_target().unwrap();
        assert_eq!(
            PointsToContext::type_variable_from_abstract_id(aid).get_name(),
            "instr_001015ba_2@RAX"
        );

        assert_eq!(
            offset.try_to_offset().expect("offset should be singleton"),
            0
        );
    }

    #[test]
    fn test_mooosl_store_abstract_object() {
        let target_bin_path = test_data_dir("mooosl");
        let bin =
            InferenceJob::parse_binary(&target_bin_path).expect("should be able to parse mooosl");
        let project = InferenceJob::parse_project(&test_data_dir("mooosl.json"), &bin)
            .expect("Should get cwe checker project");

        let rt_mem = InferenceJob::get_runtime_image(&project, &bin)
            .expect("Should be able to load bin bytes");
        let cfg = InferenceJob::graph_from_project(&project);

        let analysis_results = AnalysisResults::new(&bin, &rt_mem, &cfg, &project);

        let (res, logs) = analysis_results.compute_function_signatures();
        logs.iter().for_each(crate::util::log_cwe_message);

        let analysis_results = analysis_results.with_function_signatures(Some(&res));

        let pts_to_ctx = run_analysis(&analysis_results, DEFAULT_PTR_CONFIG.clone())
            .expect("analysis should succeed");
        let (ndidx, nd_body) =
            find_ndidx_for_block("001015bf", &cfg).expect("should have allocating block");
        let ctx = pts_to_ctx
            .get(&ndidx)
            .expect("should have context for target");

        let rax = Variable {
            name: "RAX".to_owned(),
            size: ByteSize::new(8),
            is_temp: false,
        };

        // we have the block that is the return from calloc so we should have an abstract loc in RAX
        let data_dom = ctx.pointer_state.state.eval(&Expression::Var(rax.clone()));
        assert!(data_dom.get_if_unique_target().is_some());
        let (aid, offset) = data_dom.get_if_unique_target().unwrap();
        assert_eq!(
            PointsToContext::type_variable_from_abstract_id(aid).get_name(),
            "instr_001015ba_2@RAX"
        );

        assert_eq!(
            offset.try_to_offset().expect("offset should be singleton"),
            0
        );

        // check that the store into the stack gets resolved reasonably
        let after_store_to_stack_ctx = fast_forward_pointer_state_until_address_term(
            ctx.clone(),
            "001015c3",
            nd_body.get_block(),
        );

        check_target_stack_value(&after_store_to_stack_ctx, &rt_mem);

        // now see if we preserve that abstract state to the actual store we want a constraint from
        let (str_block_idx, str_block) =
            find_ndidx_for_block("00101609", &cfg).expect("Should have storing block");

        let str_ctx = pts_to_ctx
            .get(&str_block_idx)
            .expect("should have pts ctx for store block");

        check_target_stack_value(&str_ctx, &rt_mem);

        let before_store_to_field = fast_forward_pointer_state_until_address_term(
            str_ctx.clone(),
            "0010160f",
            str_block.get_block(),
        );

        check_target_stack_value(&before_store_to_field, &rt_mem);

        // The store in the simplified IR doesnt actually happen on RAX and happens on a tempt UC0000
        let rax_tmp = Variable {
            name: "$Uc000".to_owned(),
            size: ByteSize::new(8),
            is_temp: true,
        };

        let data_dom_rax_before_field_store = before_store_to_field
            .pointer_state
            .state
            .eval(&Expression::Var(rax_tmp));

        assert!(!data_dom_rax_before_field_store.is_empty());
        assert!(!data_dom_rax_before_field_store.contains_top());

        assert!(!data_dom_rax_before_field_store
            .get_absolute_value()
            .is_some());

        assert_eq!(
            data_dom_rax_before_field_store.get_relative_values().len(),
            1
        );

        assert!(data_dom_rax_before_field_store
            .get_if_unique_target()
            .is_some());
        let (aid_field_store, offset_field_store) = data_dom_rax_before_field_store
            .get_if_unique_target()
            .unwrap();

        assert_eq!(
            PointsToContext::type_variable_from_abstract_id(aid_field_store).get_name(),
            "instr_001015ba_2@RAX"
        );

        assert_eq!(
            offset_field_store
                .try_to_offset()
                .expect("offset should be singleton"),
            0
        );
    }
}
