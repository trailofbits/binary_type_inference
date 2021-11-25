/// The constructed Transducer recogonizes the following relation:
/// Let V = Vi U Vu where Vi are the interesting type variables and Vu are the uninnteresting type varaibles. (all proofs are done under the normal form described in Appendix B.)
/// Then given a constraint set C that derives the following judgement C ⊢ X.u ⊑ Y.v:
///
struct Transducer {}

#[cfg(test)]
mod tests {
    use crate::constraints::{DerivedTypeVar, Field, FieldLabel, SubtypeConstraint, TypeVariable};

    #[test]
    fn constraints_linked_list() {
        /*
           constraints.add(SchemaParser.parse_constraint("F.in_0 ⊑ δ"))
        constraints.add(SchemaParser.parse_constraint("α ⊑ φ"))
        constraints.add(SchemaParser.parse_constraint("δ ⊑ φ"))
        constraints.add(SchemaParser.parse_constraint("φ.load.σ4@0 ⊑ α"))
        constraints.add(SchemaParser.parse_constraint("φ.load.σ4@4 ⊑ α'"))
        constraints.add(SchemaParser.parse_constraint("α' ⊑ close.in_0"))
        constraints.add(SchemaParser.parse_constraint("close.out ⊑ F.out"))
        constraints.add(SchemaParser.parse_constraint("close.in_0 ⊑ #FileDescriptor"))
        constraints.add(SchemaParser.parse_constraint("#SuccessZ ⊑ close.out"))
        */
        let proc_stack = TypeVariable::new("closed_last@sp".to_owned());
        let fvar = TypeVariable::new("closed_last".to_owned());
        let arg_tv = TypeVariable::new("closed_last_arg0".to_owned());

        let param_0 = DerivedTypeVar::new(fvar).create_with_label(FieldLabel::In(0));

        let arg_0 = DerivedTypeVar::new(arg_tv);

        let edx0 = DerivedTypeVar::new(TypeVariable::new("closed_last_edx0".to_owned()));

        let arg_0_locator = DerivedTypeVar::new(proc_stack.clone())
            .create_with_label(FieldLabel::Store)
            .create_with_label(FieldLabel::Field(Field::new(12, 32)));

        let arg_0_locator_load = DerivedTypeVar::new(proc_stack)
            .create_with_label(FieldLabel::Load)
            .create_with_label(FieldLabel::Field(Field::new(12, 32)));

        // in the example the list is a non memory object so we'll get a fresh type variable to represent it since there is no points to
        //let list_tv = DerivedTypeVar::new()

        let _cons = vec![
            SubtypeConstraint::new(param_0.clone(), arg_0.clone()),
            SubtypeConstraint::new(arg_0.clone(), arg_0_locator.clone()),
            SubtypeConstraint::new(arg_0_locator_load, edx0),
        ];
    }
}
