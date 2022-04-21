use crate::pb_constraints;
use alga::general::Multiplicative;
use alga::general::{AbstractMagma, AbstractSemigroup, Identity, TwoSidedInverse};
use alga_derive::Alga;
use cwe_checker_lib::intermediate_representation::Tid;
use log::error;
use nom::branch::alt;
use nom::bytes::complete::take_while;
use nom::character::complete::{digit1, space0};
use nom::combinator::map_res;
use nom::error::ParseError;
use nom::multi::{many0, separated_list0};
use nom::sequence::preceded;
use nom::{bytes::complete::tag, combinator::map, sequence::tuple, IResult};
use nom::{AsChar, InputTakeAtPosition};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Display, Write};
use std::iter::FromIterator;
use std::num::ParseIntError;
use std::ops::{Deref, DerefMut};
use std::vec::Vec;

fn identifier_char<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
    T: InputTakeAtPosition,
    <T as InputTakeAtPosition>::Item: AsChar,
{
    input.split_at_position1_complete(
        |x| {
            let chr = x.as_char();
            chr != '$' && chr != '_' && !chr.is_alphanumeric()
        },
        nom::error::ErrorKind::AlphaNumeric,
    )
}

pub fn parse_identifier(input: &str) -> IResult<&str, &str> {
    identifier_char(input)
}

pub fn parse_type_variable_with_cs_tag(input: &str) -> IResult<&str, TypeVariable> {
    map_res::<_, _, _, _, ParseIntError, _, _>(
        tuple((parse_identifier, tag(":"), digit1)),
        |(id, _, ctr): (&str, &str, &str)| {
            // NOTE(Ian): This is a hack to allow creating tags in tests
            let mut fake_id = String::new();
            fake_id.push_str("fakeidforctrtags_");
            fake_id.push_str(ctr);
            Ok(TypeVariable::with_tag(
                id.to_owned(),
                Tid::create(fake_id, ctr.to_owned()),
            ))
        },
    )(input)
}

pub fn parse_type_variable_without_cs_tag(input: &str) -> IResult<&str, TypeVariable> {
    map(identifier_char, |s: &str| TypeVariable::new(s.to_owned()))(input)
}

/// Parses a non-derived type variable. A type variable is just an identifier.
pub fn parse_type_variable(input: &str) -> IResult<&str, TypeVariable> {
    alt((
        parse_type_variable_with_cs_tag,
        parse_type_variable_without_cs_tag,
    ))(input)
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

fn parse_in_field(input: &str) -> IResult<&str, FieldLabel> {
    map_res::<_, _, _, _, ParseIntError, _, _>(preceded(tag("in_"), digit1), |x: &str| {
        let cons = x.parse()?;
        Ok(FieldLabel::In(cons))
    })(input)
}

/// Parses a field lable that occurs after a "." to create a derived type variable.
pub fn parse_field_label(input: &str) -> IResult<&str, FieldLabel> {
    alt((
        map(tag("load"), |_| FieldLabel::Load),
        map(tag("store"), |_| FieldLabel::Store),
        map(tag("out"), |_| FieldLabel::Out(0)),
        parse_in_field,
        parse_field_field,
        parse_add_field,
    ))(input)
}

/// Parses an optional set of fields after a type variable to create a derived type variable.
pub fn parse_fields(input: &str) -> IResult<&str, Vec<FieldLabel>> {
    many0(preceded(tag("."), parse_field_label))(input)
}

/// Parses a derived variable, including its field labels.
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

/// Parses a subtyping constraint "a.x <= b.y"
pub fn parse_subtype_cons(input: &str) -> IResult<&str, TyConstraint> {
    let parser = tuple((
        parse_derived_type_variable,
        space0,
        tag("<="),
        space0,
        parse_derived_type_variable,
    ));
    map(parser, |(x, _, _, _, y)| {
        TyConstraint::SubTy(SubtypeConstraint::new(x, y))
    })(input)
}

/// Checks for the existence of some whitespace that delimits two parsers.
pub fn parse_whitespace_delim(input: &str) -> IResult<&str, &str> {
    preceded(
        alt((tag(" "), tag("\n"), tag("\t"), tag("\r\n"))),
        take_while(|x: char| x == ' ' || x == '\n' || x == '\t'),
    )(input)
}

/// parse add constraint
pub fn parse_add_cons(input: &str) -> IResult<&str, TyConstraint> {
    map(
        tuple((
            tag("AddCons("),
            parse_derived_type_variable,
            tag(","),
            parse_derived_type_variable,
            tag(","),
            parse_derived_type_variable,
            tag(")"),
        )),
        |(_, dtv_lhs, _, dtv_rhs, _, dtv_res, _)| {
            TyConstraint::AddCons(AddConstraint::new(dtv_lhs, dtv_rhs, dtv_res))
        },
    )(input)
}

/// Parses a set of subtyping constraints delimited by whitespace between the constraints.
pub fn parse_constraint_set(input: &str) -> IResult<&str, ConstraintSet> {
    let parse_cons = alt((parse_add_cons, parse_subtype_cons));
    map(separated_list0(parse_whitespace_delim, parse_cons), |x| {
        ConstraintSet(BTreeSet::from_iter(x.into_iter()))
    })(input.trim())
}

/// A static type variable with a name
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct TypeVariable {
    name: String,
    cs_tag: Option<Tid>,
}

impl TypeVariable {
    pub fn with_tag(name: String, cs_tag: Tid) -> TypeVariable {
        TypeVariable {
            name,
            cs_tag: Some(cs_tag),
        }
    }

    pub fn get_tag(&self) -> &Option<Tid> {
        &self.cs_tag
    }

    pub fn to_callee(&self) -> TypeVariable {
        TypeVariable::new(self.name.clone())
    }

    pub fn get_cs_tag(&self) -> &Option<Tid> {
        &self.cs_tag
    }

    /// Create a new type variable with the given name
    pub fn new(name: String) -> TypeVariable {
        //TODO(ian): Maybe we should check the validity of the name here.
        TypeVariable { name, cs_tag: None }
    }

    /// Gets the string of the identifier for this type variable.
    pub fn get_name(&self) -> String {
        if let Some(cs_tag) = &self.cs_tag {
            format!("{}:{}", self.name, cs_tag)
        } else {
            self.name.clone()
        }
    }
}

impl Display for TypeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.get_name())?;
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
        TypeVariable::new(next_name)
    }

    pub fn fresh_loop_breaker(&mut self) -> TypeVariable {
        let next_name = format!("loop_breaker{}", self.curr_id.to_string());
        self.curr_id += 1;
        TypeVariable::new(next_name)
    }
}

impl Default for VariableManager {
    fn default() -> Self {
        VariableManager::new()
    }
}

/// A field constraint of the form .σN@k where N is the bit-width of the field at byte offset k
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Field {
    /// Offset in bytes of the field.
    pub offset: i64,
    /// Size of the field in bits.
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
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
/// Variance describes the relation between a field and a subtyping relation. Variance forms a multiplicative sign monoid such that
/// cov*cov = cov, contra*contra=cov, contra*cov=cov*contra=contra
pub enum Variance {
    /// This variance is covariant such that A <= B /\ B.l  ===> A.l <= B.l
    Covariant,
    /// This variance is contravariant such that A <= B /\ B.l ===> B.l <= A.l
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash, Ord, Deserialize, Serialize)]
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
    pub fn has_add_field(&self) -> bool {
        self.get_field_labels()
            .iter()
            .any(|x| matches!(x, FieldLabel::Add(_)))
    }

    /// Creates a derived type variable with no field labels.
    pub fn new(base_var: TypeVariable) -> DerivedTypeVar {
        DerivedTypeVar {
            var: base_var,
            labels: vec![],
        }
    }

    /// Checks if this derived variable is contained by the other type variable. This means the derived
    /// type variable has strictly less field labels and all field labels that do exist are represented in order on other.
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

    /// Creates a type variable that has the given path of field labels.
    pub fn create_with_path(base: TypeVariable, path: Vec<FieldLabel>) -> DerivedTypeVar {
        DerivedTypeVar {
            var: base,
            labels: path,
        }
    }

    /// Gets a reference to all field labels in order.
    pub fn get_field_labels(&self) -> &[FieldLabel] {
        &self.labels
    }

    pub fn is_formal_dtv(&self) -> bool {
        self.var.cs_tag.is_none()
    }

    pub fn refers_to_in_parameter(&self) -> bool {
        self.labels.len() >= 1 && matches!(self.labels[0], FieldLabel::In(_))
    }

    pub fn refers_to_out_parameter(&self) -> bool {
        self.labels.len() >= 1 && matches!(self.labels[0], FieldLabel::Out(_))
    }

    pub fn is_in_parameter(&self) -> bool {
        self.labels.len() == 1 && self.refers_to_in_parameter()
    }

    pub fn is_out_parameter(&self) -> bool {
        self.labels.len() == 1 && self.refers_to_out_parameter()
    }

    /// Gets the base type variable to which field labels are applied to create this derived type variable.
    pub fn get_base_variable(&self) -> &TypeVariable {
        &self.var
    }

    /// Adds a field label to this derived type variable's list of field lables. Adds to the end of the list.
    pub fn add_field_label(&mut self, lab: FieldLabel) {
        self.labels.push(lab);
    }

    /// Removes any callsite tags
    pub fn to_callee(&self) -> DerivedTypeVar {
        DerivedTypeVar::create_with_path(self.var.to_callee(), self.labels.clone())
    }
}

impl TryFrom<pb_constraints::Field> for Field {
    type Error = anyhow::Error;

    fn try_from(value: pb_constraints::Field) -> Result<Self, Self::Error> {
        let offset = value.byte_offset.try_into()?;
        let size = value.bit_size.try_into()?;
        Ok(Field { offset, size })
    }
}

impl TryFrom<pb_constraints::FieldLabel> for FieldLabel {
    type Error = anyhow::Error;

    fn try_from(value: pb_constraints::FieldLabel) -> Result<Self, Self::Error> {
        let inner = value
            .inner_type
            .ok_or(anyhow::anyhow!("No inner_type for field label"))?;
        match inner {
            pb_constraints::field_label::InnerType::Ptr(ptr_ty) => {
                match pb_constraints::Pointer::from_i32(ptr_ty)
                    .unwrap_or(pb_constraints::Pointer::LoadUnspecified)
                {
                    pb_constraints::Pointer::LoadUnspecified => Ok(FieldLabel::Load),
                    pb_constraints::Pointer::Store => Ok(FieldLabel::Store),
                }
            }
            pb_constraints::field_label::InnerType::InParam(idx) => {
                let idx = idx.try_into()?;
                Ok(FieldLabel::In(idx))
            }
            pb_constraints::field_label::InnerType::OutParam(idx) => {
                let idx = idx.try_into()?;
                Ok(FieldLabel::Out(idx))
            }
            pb_constraints::field_label::InnerType::Field(fld) => {
                let fld = Field::try_from(fld)?;
                Ok(FieldLabel::Field(fld))
            }
        }
    }
}

impl TryFrom<pb_constraints::DerivedTypeVariable> for DerivedTypeVar {
    type Error = anyhow::Error;

    fn try_from(dtv: pb_constraints::DerivedTypeVariable) -> Result<Self, Self::Error> {
        let bv = dtv.base_var;

        let labels = dtv
            .field_labels
            .into_iter()
            .map(|f| FieldLabel::try_from(f))
            .collect::<Result<Vec<FieldLabel>, Self::Error>>()?;

        Ok(DerivedTypeVar {
            var: TypeVariable::new(bv),
            labels,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
pub struct AdditionalConstraint {
    pub constraint: SubtypeConstraint,
    pub associated_variable: Tid,
}

impl TryFrom<pb_constraints::AdditionalConstraint> for AdditionalConstraint {
    type Error = anyhow::Error;

    fn try_from(value: pb_constraints::AdditionalConstraint) -> Result<Self, Self::Error> {
        let constraint = value
            .sub_ty
            .ok_or(anyhow::anyhow!("No constraint in addsubty"))
            .and_then(|orig_cons| SubtypeConstraint::try_from(orig_cons))?;

        let associated_variable = value
            .target_variable
            .ok_or(anyhow::anyhow!("No tid in addsubty"))
            .map(|tid| Tid::create(tid.name, tid.address))?;
        Ok(AdditionalConstraint {
            constraint,
            associated_variable,
        })
    }
}

/// Expresses a subtyping constraint of the form lhs ⊑ rhs
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
pub struct SubtypeConstraint {
    /// The left hand side of the subtyping constraint
    pub lhs: DerivedTypeVar,
    /// The right hand side of the subtyping constraint
    pub rhs: DerivedTypeVar,
}

impl TryFrom<pb_constraints::SubtypingConstraint> for SubtypeConstraint {
    type Error = anyhow::Error;

    fn try_from(value: pb_constraints::SubtypingConstraint) -> Result<Self, Self::Error> {
        let lhs = value
            .lhs
            .ok_or(anyhow::anyhow!("No lhs in dtv"))
            .and_then(|x| DerivedTypeVar::try_from(x))?;
        let rhs = value
            .rhs
            .ok_or(anyhow::anyhow!("No rhs in dtv"))
            .and_then(|x| DerivedTypeVar::try_from(x))?;

        Ok(SubtypeConstraint { lhs, rhs })
    }
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ConstraintSet(BTreeSet<TyConstraint>);

impl ConstraintSet {
    pub fn forget_add_constraints(self) -> ConstraintSet {
        ConstraintSet(
            self.0
                .into_iter()
                .filter(|cons| match cons {
                    TyConstraint::AddCons(_) => false,
                    TyConstraint::SubTy(sty) => {
                        !sty.lhs.has_add_field() && !sty.lhs.has_add_field()
                    }
                })
                .collect(),
        )
    }
}

/// Constraints the representation type variable to the addition of two dynamic ty vars
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AddConstraint {
    /// lhs added type repr
    pub lhs_ty: DerivedTypeVar,
    /// rhs added type var
    pub rhs_ty: DerivedTypeVar,
    /// the type variable of the result
    pub repr_ty: DerivedTypeVar,
}

impl AddConstraint {
    /// Creates an add constraint between two added derived type variables. lhs and rhs are the represented types that are added,
    /// repr is the type variable for the result.
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
        match self {
            Self::SubTy(sub) => write!(f, "{}", sub),
            Self::AddCons(add_cons) => write!(f, "{}", add_cons),
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
    use crate::constraints::TyConstraint;

    use super::{
        parse_derived_type_variable, parse_subtype_cons, DerivedTypeVar, FieldLabel,
        SubtypeConstraint, TypeVariable,
    };

    #[test]
    fn parse_simple_dtv() {
        assert_eq!(
            Ok(("", DerivedTypeVar::new(TypeVariable::new("x".to_owned())),)),
            parse_derived_type_variable("x"),
        );
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
                TyConstraint::SubTy(SubtypeConstraint::new(
                    DerivedTypeVar::new(TypeVariable::new("x".to_owned())),
                    DerivedTypeVar::new(TypeVariable::new("y".to_owned())),
                ))
            )),
            parse_subtype_cons("x <= y"),
        );
    }

    #[test]
    fn parse_func_cons() {
        let mut func = DerivedTypeVar::new(TypeVariable::new("sub_00001000".to_owned()));
        func.add_field_label(FieldLabel::Out(0));
        assert_eq!(
            Ok((
                "",
                TyConstraint::SubTy(SubtypeConstraint::new(
                    func,
                    DerivedTypeVar::new(TypeVariable::new("int".to_owned())),
                ))
            )),
            parse_subtype_cons("sub_00001000.out <= int"),
        );
    }

    // file_descriptor <= sub_00001000.in_0
    #[test]
    fn parse_func_cons2() {
        let mut func = DerivedTypeVar::new(TypeVariable::new("sub_00001000".to_owned()));
        func.add_field_label(FieldLabel::In(0));
        assert_eq!(
            Ok((
                "",
                TyConstraint::SubTy(SubtypeConstraint::new(
                    DerivedTypeVar::new(TypeVariable::new("file_descriptor".to_owned())),
                    func,
                ))
            )),
            parse_subtype_cons("file_descriptor <= sub_00001000.in_0"),
        );
    }
}
