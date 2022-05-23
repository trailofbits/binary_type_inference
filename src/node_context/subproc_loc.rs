use std::collections::BTreeSet;

use cwe_checker_lib::intermediate_representation::Arg;
use cwe_checker_lib::intermediate_representation::{Expression, Variable};

use crate::constraint_generation::{ArgTvar, NodeContextMapping, SubprocedureLocators};

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
        _vm: &mut crate::constraints::VariableManager,
    ) -> BTreeSet<ArgTvar> {
        match arg {
            Arg::Register { expr, .. } => {
                if let Expression::Var(var) = expr {
                    let var_set = reg.access(var);
                    var_set
                        .into_iter()
                        .map(|x| ArgTvar::VariableTvar(x))
                        .collect()
                } else {
                    BTreeSet::new()
                }
            }
            Arg::Stack { address, size, .. } => {
                // Reason this is ok in the case of actuals: at an actual call site the stack pointer is going to be below the newly pushed EIP which is the 0 offset of the new frame.
                // Therefore the offset is safe for our current frame.

                // If it's a formal this is still valid because we add the base for that frame but the frame still points to the same 0 point.
                // Returns are less clear
                // TODO(ian): examine returns (returns cant be on the stack so do we care)?
                let accessed_pointers = points_to.points_to(&address, *size);

                accessed_pointers
                    .into_iter()
                    .map(ArgTvar::MemTvar)
                    .collect()
            }
        }
    }
}
