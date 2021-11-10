use std::collections::BTreeSet;
use std::vec::Vec;

/// A static type variable with a name
#[derive(Debug, Clone)]
pub struct TypeVariable {
    name: String,
}

/// Manages ephmeral type variables
pub struct VariableManager {
    curr_id: u64,
}

impl VariableManager {
    /// Creates a new default variable manager
    pub fn new() -> VariableManager {
        VariableManager { curr_id: 0 }
    }

    /// Creates a fresh [TypeVariable] of the form τn where n is the count of fresh variables from this manager.
    pub fn fresh(&mut self) -> TypeVariable {
        let next_name = format!("τ{}", self.curr_id.to_string());
        self.curr_id += 1;
        TypeVariable { name: next_name }
    }
}

impl Default for VariableManager {
    fn default() -> Self {
        VariableManager::new()
    }
}

/// A field constraint of the form .σN@k where N is the bit-width of the field at byte offset k
#[derive(Debug, Clone)]
pub struct Field {
    offset: i64,
    size: u64,
}

/// This function has an input parameter at the location defined by the parameter index
/// Note(Ian): In the future if we have our own solvers these locations should be extended to be more
/// general than indeces.
#[derive(Debug, Clone)]
pub struct In {
    param_index: u32,
}

/// A field label specifies the capabilities of a [DerivedTypeVar]
#[derive(Debug, Clone)]
pub enum FieldLabel {
    /// The previous label can be loaded from
    Load,
    /// The previous label can be stored to
    Store,
    /// An in parameter on the function
    In(In),
    /// A formal return on the function
    Out,
    /// A field with the specified bit width and byte offset
    Field(Field),
}

/// A derived type variable that contains the base [TypeVariable] and an ordered vector of [FieldLabel].
/// Each label is applied in order to determine the expressed capability on the base type variable.
/// Variance is determined by the sign monoid of the component [FieldLabel] variances ⊕·⊕ = ⊖·⊖ = ⊕ and ⊕·⊖ = ⊖·⊕ = ⊖
/// [DerivedTypeVar] forms the expression αw where α ∈ V and w ∈ Σ^*

#[derive(Debug, Clone)]
pub struct DerivedTypeVar {
    var: TypeVariable,
    labels: Vec<FieldLabel>,
}

/// Expresses a subtyping constraint of the form lhs ⊑ rhs
#[derive(Debug, Clone)]
pub struct SubtypeConstraint {
    lhs: DerivedTypeVar,
    rhs: DerivedTypeVar,
}

/// A set of [SubtypeConstraint]
pub struct ConstraintSet(BTreeSet<SubtypeConstraint>);
