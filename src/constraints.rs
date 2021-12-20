use alga::general::Multiplicative;
use alga::general::{
    AbstractMagma, AbstractSemigroup, Identity, MultiplicativeGroup, MultiplicativeMonoid,
    MultiplicativeSemigroup, TwoSidedInverse,
};
use alga_derive::Alga;
use cwe_checker_lib::intermediate_representation::Variable;
use log::error;
use nom::branch::alt;
use nom::bytes::complete::take_while;
use nom::character::complete::alphanumeric1;
use nom::character::complete::{anychar, char, crlf, digit1, newline, space0, tab};
use nom::character::is_newline;
use nom::combinator::map_res;
use nom::multi::{many0, many1, separated_list0};
use nom::sequence::{delimited, preceded, Tuple};
use nom::Parser;
use nom::{bytes::complete::tag, character::is_space, combinator::map, sequence::tuple, IResult};
use std::collections::{BTreeSet, VecDeque};
use std::fmt::{Debug, Display, Write};
use std::iter::FromIterator;
use std::num::ParseIntError;
use std::ops::{Deref, DerefMut};
use std::vec::Vec;

pub fn parse_type_variable(input: &str) -> IResult<&str, TypeVariable> {
    map(alphanumeric1, |s: &str| TypeVariable::new(s.to_owned()))(input)
}

fn parse_field_field(input: &str) -> IResult<&str, FieldLabel> {
    //σ{}@{}
    map_res::<_, _, _, _, ParseIntError, _, _>(
        tuple((tag("σ"), digit1, tag("@"), digit1)),
        |(_, field_size, _, offset): (&str, &str, &str, &str)| {
            let field_size: usize = field_size.parse()?;
            let offset = offset.parse()?;
            Ok(FieldLabel::Field(Field {
                size: field_size,
                offset,
            }))
        },
    )(input)
}

fn parse_add_field(input: &str) -> IResult<&str, FieldLabel> {
    map_res::<_, _, _, _, ParseIntError, _, _>(preceded(tag("+"), digit1), |x: &str| {
        let cons = x.parse()?;
        Ok(FieldLabel::Add(cons))
    })(input)
}

pub fn parse_field_label(input: &str) -> IResult<&str, FieldLabel> {
    alt((
        map(tag("load"), |_| FieldLabel::Load),
        map(tag("store"), |_| FieldLabel::Store),
        map(tag("out"), |_| FieldLabel::Out(0)),
        parse_field_field,
        parse_add_field,
    ))(input)
}

pub fn parse_fields(input: &str) -> IResult<&str, Vec<FieldLabel>> {
    many0(preceded(tag("."), parse_field_label))(input)
}

pub fn parse_derived_type_variable(input: &str) -> IResult<&str, DerivedTypeVar> {
    map(
        tuple((parse_type_variable, parse_fields)),
        |(tv, fields)| {
            let mut dv = DerivedTypeVar::new(tv);
            fields.into_iter().for_each(|x| dv.add_field_label(x));
            dv
        },
    )(input)
}

pub fn parse_subtype_cons(input: &str) -> IResult<&str, SubtypeConstraint> {
    let parser = tuple((
        parse_derived_type_variable,
        space0,
        tag("<="),
        space0,
        parse_derived_type_variable,
    ));
    map(parser, |(x, _, _, _, y)| SubtypeConstraint::new(x, y))(input)
}

pub fn parse_whitespace_delim(input: &str) -> IResult<&str, &str> {
    preceded(
        alt((tag(" "), tag("\n"), tag("\t"), tag("\r\n"))),
        take_while(|x: char| x == ' ' || x == '\n' || x == '\t'),
    )(input)
}

pub fn parse_constraint_set(input: &str) -> IResult<&str, ConstraintSet> {
    map(
        separated_list0(parse_whitespace_delim, parse_subtype_cons),
        |x| {
            ConstraintSet(BTreeSet::from_iter(
                x.into_iter().map(|x| TyConstraint::SubTy(x)),
            ))
        },
    )(input.trim())
}

/// A static type variable with a name
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeVariable {
    name: String,
}

impl TypeVariable {
    /// Create a new type variable with the given name
    pub fn new(name: String) -> TypeVariable {
        //TODO(ian): Maybe we should check the validity of the name here.
        TypeVariable { name }
    }

    pub fn get_name(&self) -> &str {
        &self.name
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Field {
    pub offset: i64,
    pub size: usize,
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl FieldLabel {
    /// Gets the variance of this field label
    pub fn variance(&self) -> Variance {
        match self {
            Self::Load => Variance::Covariant,
            Self::Store => Variance::Contravariant,
            Self::Field(_) => Variance::Covariant,
            Self::In(_) => Variance::Contravariant,
            Self::Out(_) => Variance::Covariant,
            Self::Add(_) => Variance::Covariant,
        }
    }
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Alga, Debug)]
#[alga_traits(Monoid(Multiplicative))]
pub enum Variance {
    Covariant,
    Contravariant,
}
impl Display for Variance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match &self {
            Variance::Covariant => '⊕',
            Variance::Contravariant => '⊖',
        })
    }
}

impl AbstractMagma<Multiplicative> for Variance {
    fn operate(&self, right: &Self) -> Self {
        if self == right {
            Self::Covariant
        } else {
            Self::Contravariant
        }
    }
}

impl Identity<Multiplicative> for Variance {
    fn identity() -> Self {
        Self::Covariant
    }
}

impl TwoSidedInverse<Multiplicative> for Variance {
    fn two_sided_inverse(&self) -> Self {
        Self::Contravariant
    }
}

impl AbstractSemigroup<Multiplicative> for Variance {}

/// A derived type variable that contains the base [TypeVariable] and an ordered vector of [FieldLabel].
/// Each label is applied in order to determine the expressed capability on the base type variable.
/// Variance is determined by the sign monoid of the component [FieldLabel] variances ⊕·⊕ = ⊖·⊖ = ⊕ and ⊕·⊖ = ⊖·⊕ = ⊖
/// [DerivedTypeVar] forms the expression αw where α ∈ V and w ∈ Σ^*

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash, Ord)]
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

    pub fn is_prefix_of(&self, other: &DerivedTypeVar) -> bool {
        other.get_base_variable() == self.get_base_variable()
            && self.labels.len() < other.labels.len()
            && self
                .labels
                .iter()
                .zip(other.labels.iter())
                .all(|(x, y)| x == y)
    }

    /// computes the path variance, an epsilon is by default covariant
    pub fn path_variance(&self) -> Variance {
        self.labels
            .iter()
            .map(|x| x.variance())
            .reduce(|x, y| x.operate(&y))
            .unwrap_or(Variance::Covariant)
    }

    /// Immutably add label.
    pub fn create_with_label(&self, lab: FieldLabel) -> DerivedTypeVar {
        let mut n = self.clone();
        n.add_field_label(lab);
        n
    }

    pub fn create_with_path(base: TypeVariable, path: Vec<FieldLabel>) -> DerivedTypeVar {
        DerivedTypeVar {
            var: base,
            labels: path,
        }
    }

    pub fn get_field_labels(&self) -> &[FieldLabel] {
        &self.labels
    }

    pub fn get_base_variable(&self) -> &TypeVariable {
        &self.var
    }

    /// Adds a field label to this derived type variable's list of field lables. Adds to the end of the list.
    pub fn add_field_label(&mut self, lab: FieldLabel) {
        self.labels.push(lab);
    }
}

/// Expresses a subtyping constraint of the form lhs ⊑ rhs
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubtypeConstraint {
    /// The left hand side of the subtyping constraint
    pub lhs: DerivedTypeVar,
    /// The right hand side of the subtyping constraint
    pub rhs: DerivedTypeVar,
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

#[cfg(test)]
mod test {
    use super::{
        parse_derived_type_variable, parse_subtype_cons, DerivedTypeVar, FieldLabel,
        SubtypeConstraint, TypeVariable,
    };

    #[test]
    fn parse_simple_derived_tvar() {
        #[test]
        fn parse_simple_constraint() {
            assert_eq!(
                Ok(("", DerivedTypeVar::new(TypeVariable::new("x".to_owned())),)),
                parse_derived_type_variable("x"),
            );
        }
    }

    #[test]
    fn parse_dt_var() {
        let mut dt = DerivedTypeVar::new(TypeVariable::new("x".to_owned()));
        dt.add_field_label(FieldLabel::Load);
        assert_eq!(Ok(("", dt)), parse_derived_type_variable("x.load"));
    }

    #[test]
    fn parse_simple_constraint() {
        assert_eq!(
            Ok((
                "",
                SubtypeConstraint::new(
                    DerivedTypeVar::new(TypeVariable::new("x".to_owned())),
                    DerivedTypeVar::new(TypeVariable::new("y".to_owned())),
                )
            )),
            parse_subtype_cons("x <= y"),
        );
    }
}
