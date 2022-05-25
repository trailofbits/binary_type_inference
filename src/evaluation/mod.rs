use std::fmt::Display;

use alga::general::{AbstractMagma, Additive, Lattice};

use crate::{
    constraints::FieldLabel,
    graph_algos::{explore_paths, find_node},
    solver::type_sketch::{LatticeBounds, Sketch},
};

/// The minimum type capabilities required to be used as a type bound
pub trait SketchLabelElement:
    std::cmp::PartialEq + Lattice + Clone + AbstractMagma<Additive> + Display
{
}

/// A node comparison represents the comparison of two primitive type labels that are considered equivalent
/// since they are reached by the same path.
pub struct NodeComparison<U: SketchLabelElement> {
    expected_type_bounds: LatticeBounds<U>,
    actual_type_bounds: LatticeBounds<U>,
    path: Vec<FieldLabel>,
}

/// Results from comparing a type variable's sketch to it's actual type
pub struct EvaluatedVariable<U: SketchLabelElement> {
    over_precise_language: Option<Sketch<U>>,
    missing_language: Option<Sketch<U>>,
    incorrect_node_labels: Vec<NodeComparison<U>>,
}

fn generate_node_comparisons<U>(
    expected_type: &Sketch<U>,
    actual_type: &Sketch<U>,
) -> Vec<NodeComparison<U>>
where
    U: SketchLabelElement,
{
    todo!()
    /* let target_graph = actual_type.get_graph().get_graph();
    explore_paths(actual_type.get_graph().get_graph(), actual_type.get_entry())
        .filter_map(|(reaching_eid_path, target_node)| {
            let reaching_path: Vec<FieldLabel> = reaching_eid_path
                .iter()
                .map(|x| {
                    actual_type
                        .get_graph()
                        .get_graph()
                        .edge_weight(*x)
                        .expect("Every reached edge should be in the graph")
                        .clone()
                })
                .collect::<Vec<_>>();

            let corresponding_node = find_node(
                expected_type.get_graph().get_graph(),
                expected_type.get_entry(),
                reaching_path.iter(),
            );

            corresponding_node.map(|expected_node| {
                let expec_type_bounds = expected_type
                    .get_graph()
                    .get_graph()
                    .node_weight(expected_node)
                    .expect("found node should be valid");
            })
        })
        .collect::<Vec<_>>()*/
}

pub fn compare_variable<U>(
    expected_type: &Sketch<U>,
    actual_type: &Sketch<U>,
) -> EvaluatedVariable<U>
where
    U: SketchLabelElement,
{
    let maybe_overrefined_language = actual_type.difference(expected_type);
    let maybe_missing_language = expected_type.difference(actual_type);

    let overrefined_language = if !maybe_overrefined_language.empty_language() {
        Some(maybe_overrefined_language)
    } else {
        None
    };

    let missing_language = if maybe_missing_language.empty_language() {
        Some(maybe_missing_language)
    } else {
        None
    };

    if overrefined_language.is_none() {
        // actual_type subseteq exepcted_type
        // So we can check every actual type node.
        todo!()
    } else {
        EvaluatedVariable {
            over_precise_language: overrefined_language,
            incorrect_node_labels: vec![],
            missing_language,
        }
    }
}
