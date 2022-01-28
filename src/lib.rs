//! # Type Constraint Generation by Abstract Interpretation
//!
//! Utilizes the [CWE checker pointer analysis](cwe_checker_lib::analysis::pointer_inference), reaching definitions, and parameter analysis from ghidra
//! to generate subtyping constraints of the form used in [retypd](https://github.com/GrammaTech/retypd).
#![warn(missing_docs)]
mod analysis;

/// Generates constraints as specified in [constraints] from an IR [Project](cwe_checker_lib::intermediate_representation::Project)
pub mod constraint_generation;

/// Our model of subtyping constraints
pub mod constraints;

/// Node contexts handle flow/context sensitive information for a given node's type constraints.
pub mod node_context;

#[cfg(test)]
pub(crate) mod test_utils;

/// Contains utility functions for transforming json into the project IR
pub mod util;

/// Contains an implementation of constraint solving, type sketch generation, and c type generation.
pub mod solver;

/// custom petagraph algos, specifically dense path expression from (FAST ALGORITHMS FOR SOLVING PATH PROBLEMS)[http://i.stanford.edu/pub/cstr/reports/cs/tr/79/734/CS-TR-79-734.pdf]
pub mod graph_algos;

/// Takes a sketch graph of types and lowers this type information to ctypes, using datalog defined heurisitics.
pub mod lowering;

/// Protobuf ctypes
pub mod ctypes {
    include!(concat!(env!("OUT_DIR"), "/ctypes.rs"));
}

/// Protobuf constraints
pub mod pb_constraints {
    include!(concat!(env!("OUT_DIR"), "/constraints.rs"));
}

/// Parses a context of file inputs into an inference job which can be run to retrieve generated constraints,
/// simplified constraints, and lowered types.
pub mod inference_job;

// Integration tests
#[cfg(test)]
mod tests {

    struct TestCase {
        binary_path: String,
        ir_json_path: String,
        interesting_tid_path: String,
        additional_constraints_path: String,
    }
}
