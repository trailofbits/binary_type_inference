use std::collections::BTreeSet;

use cwe_checker_lib::intermediate_representation::Arg;
use cwe_checker_lib::intermediate_representation::{Expression, Variable};

use crate::constraint_generation::{ArgTvar, NodeContextMapping, SubprocedureLocators};
use crate::constraints::ConstraintSet;

#[derive(Clone)]
/// The context for a node needed to evaluate an argument specification.
pub struct ProcedureContext {
    /// The procedure context doesnt change. It only needs to know about the stack variable for this project.
    pub stack_pointer: Variable,
}

impl NodeContextMapping for ProcedureContext {
    fn apply_def(
        &self,
        _term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Def,
        >,
    ) -> Self {
        self.clone()
    }
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
                    *size,
                    vm,
                );

                (
                    accessed_pointers
                        .into_iter()
                        .map(ArgTvar::MemTvar)
                        .collect(),
                    ConstraintSet::empty(),
                )
            }
        }
    }
}
