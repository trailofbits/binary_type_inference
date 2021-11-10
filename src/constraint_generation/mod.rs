use cwe_checker_lib::intermediate_representation::{ByteSize, Expression, Variable};

use crate::constraints::{ConstraintSet, SubtypeConstraint, TypeVariable, VariableManager};

use std::collections::btree_set::BTreeSet;

pub trait RegisterMapping {
    fn access(&self, var: &Variable, vman: &mut VariableManager) -> (TypeVariable, ConstraintSet);
}

pub trait PointsToMapping {
    fn points_to(&self, address: Expression, sz: ByteSize) -> BTreeSet<TypeVariable>;
}

pub trait SubprocedureLocators {}

/// Represents the flow-sensitive context needed by flow-insensitive constraint generation to generate type variables and constriants.
/// The register mapping provides constraints and type variables to represent a register when it is accessed via some notion of reaching definitions.
/// The PointsToMapping determines the set of a type variables a load or store points to in order to generate constraints.
/// Finally the SubprocedureLocators are used to link actual and formal arguments and returns within constraints.
pub struct Context<R: RegisterMapping, P: PointsToMapping, S: SubprocedureLocators> {
    reg_map: R,
    points_to: P,
    SubprocedureLocators: S,
}
