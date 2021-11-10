use cwe_checker_lib::intermediate_representation::{ByteSize, Expression, Variable};

use crate::constraints::{ConstraintSet, SubtypeConstraint, TypeVariable, VariableManager};

use std::collections::btree_set::BTreeSet;

/// Maps a variable (register) to it's representing type variable at this time step in the program. This type variable is some representation of
/// all reaching definitions of this register.
pub trait RegisterMapping {
    /// Creates or returns the type variable representing this register at this program point. Takes a [VariableManager] so it
    /// can create fresh type variables.
    fn access(&self, var: &Variable, vman: &mut VariableManager) -> (TypeVariable, ConstraintSet);
}

/// Maps an address expression and a size to the possible type variables representing the loaded address at this program point.
/// Implementors of this trait effectively act as memory managers for the type inference algorithm.
pub trait PointsToMapping {
    /// Gets the set of type variables this address expression points to.  Takes a [VariableManager] so it
    /// can create fresh type variables.
    fn points_to(
        &self,
        address: Expression,
        sz: ByteSize,
        vman: &mut VariableManager,
    ) -> BTreeSet<TypeVariable>;
}

/// Links formal parameters with the type variable for their actual argument at callsites.
/// Additionally, links actual returns to formal returns at return sites.
pub trait SubprocedureLocators {}

/// Represents the flow-sensitive context needed by flow-insensitive constraint generation to generate type variables and constriants.
/// The register mapping provides constraints and type variables to represent a register when it is accessed via some notion of reaching definitions.
/// The PointsToMapping determines the set of a type variables a load or store points to in order to generate constraints.
/// Finally the SubprocedureLocators are used to link actual and formal arguments and returns within constraints.
pub struct Context<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators> {
    reg_map: R,
    points_to: P,
    subprocedure_locators: S,
}
