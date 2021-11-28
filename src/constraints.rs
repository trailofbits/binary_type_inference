use log::error;
use std::collections::BTreeSet;
use std::fmt::{write, Debug, Display, Write};
use std::ops::{Deref, DerefMut};
use std::vec::Vec;

/// A static type variable with a name
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeVariable {
    name: String,
}

impl TypeVariable {
    /// Create a new type variable with the given name
    pub fn new(name: String) -> TypeVariable {
        //TODO(ian): Maybe we should check the validity of the name here.
        TypeVariable { name }
    }
}

impl Display for TypeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)?;
        Ok(())
    }
}

/// Manages ephemeral type variables
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Field {
    offset: i64,
    size: usize,
}

impl Field {
    /// creates a new field access at a byte offset and bit-width size.
    pub fn new(offset: i64, size: usize) -> Field {
        Field { offset, size }
    }
}

impl Display for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("σ{}@{}", self.size, self.offset))
    }
}

/// This function has an input parameter at the location defined by the parameter index
/// Note(Ian): In the future if we have our own solvers these locations should be extended to be more
/// general than indeces.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct In {
    /// The parameter index starting from 0
    pub param_index: usize,
}

/// A field label specifies the capabilities of a [DerivedTypeVar]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FieldLabel {
    /// The previous label can be loaded from
    Load,
    /// The previous label can be stored to
    Store,
    /// An in parameter on the function
    In(usize),
    /// A formal return on the function
    Out(usize),
    /// A field with the specified bit width and byte offset
    Field(Field),
    ///The type variable with the addition of a constant offset
    Add(i128),
}

impl Display for FieldLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldLabel::Load => f.write_str("load"),
            FieldLabel::Store => f.write_str("store"),
            &FieldLabel::Add(offset) => f.write_fmt(format_args!("+{}", offset)),
            FieldLabel::In(ind) => f.write_fmt(format_args!("in_{}", ind)),
            FieldLabel::Out(ind) => {
                if *ind != 0 {
                    error!("Multi return field label cannot be converted to retypd constraints");
                }
                f.write_str("out")
            }
            FieldLabel::Field(field) => write!(f, "{}", field),
        }
    }
}

/// A derived type variable that contains the base [TypeVariable] and an ordered vector of [FieldLabel].
/// Each label is applied in order to determine the expressed capability on the base type variable.
/// Variance is determined by the sign monoid of the component [FieldLabel] variances ⊕·⊕ = ⊖·⊖ = ⊕ and ⊕·⊖ = ⊖·⊕ = ⊖
/// [DerivedTypeVar] forms the expression αw where α ∈ V and w ∈ Σ^*

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DerivedTypeVar {
    var: TypeVariable,
    labels: Vec<FieldLabel>,
}

impl Display for DerivedTypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.var)?;
        for l in self.labels.iter() {
            f.write_char('.')?;
            write!(f, "{}", l)?;
        }
        Ok(())
    }
}

impl DerivedTypeVar {
    /// Creates a derived type variable with no field labels.
    pub fn new(base_var: TypeVariable) -> DerivedTypeVar {
        DerivedTypeVar {
            var: base_var,
            labels: vec![],
        }
    }

    /// Immutably add label.
    pub fn create_with_label(&self, lab: FieldLabel) -> DerivedTypeVar {
        let mut n = self.clone();
        n.add_field_label(lab);
        n
    }

    /// Adds a field label to this derived type variable's list of field lables. Adds to the end of the list.
    pub fn add_field_label(&mut self, lab: FieldLabel) {
        self.labels.push(lab);
    }
}

/// Expresses a subtyping constraint of the form lhs ⊑ rhs
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubtypeConstraint {
    lhs: DerivedTypeVar,
    rhs: DerivedTypeVar,
}

impl SubtypeConstraint {
    /// Create a subtype constraint where lhs is a subtype of rhs.
    pub fn new(lhs: DerivedTypeVar, rhs: DerivedTypeVar) -> SubtypeConstraint {
        SubtypeConstraint { lhs, rhs }
    }
}

impl Display for SubtypeConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ⊑ {}", self.lhs, self.rhs)
    }
}

/// A set of [SubtypeConstraint]
#[derive(Debug)]
pub struct ConstraintSet(BTreeSet<TyConstraint>);

/// Constraints the representation type variable to the addition of two dynamic ty vars
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AddConstraint {
    /// lhs added type repr
    lhs_ty: DerivedTypeVar,
    /// rhs added type var
    rhs_ty: DerivedTypeVar,
    /// the type variable of the result
    repr_ty: DerivedTypeVar,
}

impl AddConstraint {
    pub fn new(
        lhs_ty: DerivedTypeVar,
        rhs_ty: DerivedTypeVar,
        repr_ty: DerivedTypeVar,
    ) -> AddConstraint {
        AddConstraint {
            lhs_ty,
            rhs_ty,
            repr_ty,
        }
    }
}

impl Display for AddConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Add({},{},{})", self.lhs_ty, self.rhs_ty, self.repr_ty)
    }
}

/// A constraint on type variables
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyConstraint {
    /// lhs is a subtype of rhs
    SubTy(SubtypeConstraint),
    /// repr is the type resulting from the addition of two types added together
    AddCons(AddConstraint),
}

impl Display for TyConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            &Self::SubTy(sub) => write!(f, "{}", sub),
            &Self::AddCons(add_cons) => write!(f, "{}", add_cons),
        }
    }
}

impl ConstraintSet {
    /// Insert all the constraints from [cons] into this constraint set.
    pub fn insert_all(&mut self, cons: &ConstraintSet) {
        cons.0.iter().cloned().for_each(|con| {
            self.0.insert(con);
        });
    }

    /// A singleton constraint set with one subtyping relation.
    pub fn singleton(cons: SubtypeConstraint) -> ConstraintSet {
        let mut emp = ConstraintSet::empty();
        emp.insert(TyConstraint::SubTy(cons));
        emp
    }

    /// An empty constraint set
    pub fn empty() -> ConstraintSet {
        ConstraintSet(BTreeSet::new())
    }
}

impl From<BTreeSet<TyConstraint>> for ConstraintSet {
    fn from(c: BTreeSet<TyConstraint>) -> Self {
        ConstraintSet(c)
    }
}

impl Default for ConstraintSet {
    fn default() -> ConstraintSet {
        ConstraintSet(BTreeSet::new())
    }
}

impl Display for ConstraintSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for cons in self.0.iter() {
            writeln!(f, "{}", cons)?;
        }

        Ok(())
    }
}

impl Deref for ConstraintSet {
    type Target = BTreeSet<TyConstraint>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ConstraintSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
