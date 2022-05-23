/// This analysis agressively adds formal outs to functions that ghidra did not detect formal outs for.
/// This handles cases like:
///   atoi((char *)&local_28);
///  if (local_10 != *(long *)(in_FS_OFFSET + 0x28)) {
///        __stack_chk_fail();
/// }
/// return;
/// }
///  Where atoi's return is shared through the calling function and there is a path that calls a no return function.
/// This analysis depends on reaching definitions. If a function does not have formal outs we check if a called functions returns are alive at a return
/// If they are, we add that function's reaching formals as returns to the current function.
use std::collections::HashMap;

use cwe_checker_lib::{
    intermediate_representation::{Arg, Blk, Jmp, Project, Sub, Term, Tid},
};


use crate::{
    analysis::reaching_definitions::Definition, constraint_generation::NodeContextMapping,
    node_context::register_map::RegisterContext,
};

pub struct Context<'a> {
    reaching_defs_start_of_block: HashMap<Tid, RegisterContext>,
    ir: &'a mut Project,
}

impl Context<'_> {
    pub fn new<'a>(
        ir: &'a mut Project,
        reaching_defs_start_of_block: HashMap<Tid, RegisterContext>,
    ) -> Context<'a> {
        Context {
            reaching_defs_start_of_block,
            ir,
        }
    }

    fn get_returns_from_block(&self, blk: &Term<Blk>) -> Option<Vec<Arg>> {
        self.reaching_defs_start_of_block
            .get(&blk.tid)
            .map(|reg_context| {
                // NOTE(Ian): So you might be thinking, hey you dont apply conditional branches to the abstract state.
                // You are absolutely correct, however, in this very specific case it's not needed because reaching definitions cannot be refined
                // by a conditional branch (not easily anyways). So pragmatically since this feature of applying conditional branches wasnt needed in constraint generation
                // (we can just use the computed post conditions) we decide to not apply here.

                let context_before_jumps = blk
                    .term
                    .defs
                    .iter()
                    .fold(reg_context.clone(), |cont, df| cont.apply_def(df));
                // so we can return here so check if return is live
                let vars_to_defs = context_before_jumps.get_register_context();
                vars_to_defs
                    .iter()
                    .filter(|(_v, tset)| {
                        tset.iter()
                            .any(|t| matches!(t, &Definition::ActualRet(_, _)))
                    })
                    .map(|(v, _)| Arg::Register {
                        expr: cwe_checker_lib::intermediate_representation::Expression::Var(
                            v.clone(),
                        ),
                        // TODO(ian): copy over datatype
                        data_type: None,
                    })
                    .collect()
            })
    }

    fn generate_returns_for_sub(&self, sub: &Term<Sub>) -> Vec<Arg> {
        sub.term
            .blocks
            .iter()
            .filter(|blk| {
                blk.term.jmps.iter().any(|jmp| {
                    let jmp = &jmp.term;
                    matches!(jmp, Jmp::Return(_))
                })
            })
            .map(|blk| self.get_returns_from_block(blk))
            .find(|x| x.is_some())
            .unwrap_or(Some(vec![]))
            .unwrap_or(vec![])
    }

    fn collect_returns(&self) -> HashMap<Tid, Vec<Arg>> {
        let mut tot = HashMap::new();
        for (_, func) in self.ir.program.term.subs.iter() {
            if func.term.formal_rets.is_empty() {
                tot.insert(func.tid.clone(), self.generate_returns_for_sub(func));
            }
        }

        tot
    }

    pub fn apply_psuedo_returns(&mut self) {
        let m = self.collect_returns();
        for (_, sub) in self.ir.program.term.subs.iter_mut() {
            if let Some(new_rets) = m.get(&sub.tid) {
                sub.term.formal_rets = new_rets.clone();
            }
        }
    }
}
