use std::collections::BTreeSet;

use cwe_checker_lib::intermediate_representation::Arg;
use cwe_checker_lib::intermediate_representation::{Expression, Variable};

use crate::constraint_generation::{ArgTvar, SubprocedureLocators};
use crate::constraints::ConstraintSet;

#[derive(Clone)]
pub struct ProcedureContext {
    // the procedure context doesnt change
    pub stack_pointer: Variable,
}

impl SubprocedureLocators for ProcedureContext {
    fn get_type_variables_and_constraints_for_arg(
        &self,
        arg: &Arg,
        reg: &impl crate::constraint_generation::RegisterMapping,
        points_to: &impl crate::constraint_generation::PointsToMapping,
        vm: &mut crate::constraints::VariableManager,
    ) -> (BTreeSet<ArgTvar>, ConstraintSet) {
        match arg {
            Arg::Register { var, .. } => {
                let (var, cons) = reg.access(var, vm);
                let mut tvset = BTreeSet::new();
                tvset.insert(ArgTvar::VariableTvar(var));
                (tvset, cons)
            }
            Arg::Stack { offset, size, .. } => {
                let accessed_pointers = points_to.points_to(
                    &Expression::Var(self.stack_pointer.clone()).plus_const(*offset),
                    size.clone(),
                    vm,
                );

                (
                    accessed_pointers
                        .into_iter()
                        .map(|tv_access| ArgTvar::MemTvar(tv_access))
                        .collect(),
                    ConstraintSet::empty(),
                )
            }
        }
    }
}
