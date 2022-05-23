/// Builds a callgraph of TIDs (only considering direct/ resolved control flow).
pub mod callgraph;
/// Adds returns to the formal return parameters of procedures that tail call procedures with a return value.
pub mod fixup_returns;
/// Analyzes the reaching definitions for variables in this project. Maps Tids to register contexts.
pub mod reaching_definitions;
/// Currently unused but finds the maximum stack depth of a given procedure.
pub mod stack_depth_analysis;
