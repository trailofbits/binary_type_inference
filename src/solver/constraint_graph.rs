use crate::constraints::{ConstraintSet, DerivedTypeVar, TyConstraint, Variance};
use petgraph::{data::Build, graph::NodeIndex, Directed, Graph};
use std::{collections::HashMap, rc::Rc};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Direction {
    Lhs,
    Rhs,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TypeVariable {
    Interesting(DerivedTypeVar, Direction),
    Uninteresting(DerivedTypeVar),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TypeVarControlState {
    dt_var: TypeVariable,
    variance: Variance,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ControlState {
    Start,
    End,
    TypeVarControlState,
}

/// The constructed Transducer recogonizes the following relation:
/// Let V = Vi U Vu where Vi are the interesting type variables and Vu are the uninnteresting type varaibles. (all proofs are done under the normal form described in Appendix B.)
/// Then given a constraint set C that derives the following judgement C ⊢ X.u ⊑ Y.v:
struct Transducer {
    /// You might say... why not just have this be a reference in a graphmap? You'd be correct but then we'd need some place to hold
    /// type variables that are generated during loop breaking.
    grph: Graph<ControlState, (), Directed>,
    nd_to_index: HashMap<ControlState, NodeIndex>,
}

impl Transducer {
    pub fn new(cons: &ConstraintSet) -> Transducer {
        let mut grph = Graph::new();
        let mut nd_to_index: HashMap<DerivedTypeVar, NodeIndex> = HashMap::new();

        for constraint in cons.iter() {
            //TODO:(ian) Add constraints should be handled during the second pass of sketch generation I think
            if let TyConstraint::SubTy(sub) = constraint {
                let src = *nd_to_index
                    .entry(sub.lhs.clone())
                    .or_insert_with(|| grph.add_node(sub.lhs.clone()));

                let dst = nd_to_index
                    .entry(sub.rhs.clone())
                    .or_insert_with(|| grph.add_node(sub.rhs.clone()));

                grph.add_edge(src, *dst, ());
            }
        }

        Transducer { grph, nd_to_index }
    }

    pub fn saturate(&mut self) {}

    pub fn break_loops(&mut self) {}
}

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
