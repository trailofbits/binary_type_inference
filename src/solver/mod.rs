/// Converts schemes of type constraints to sketches.
pub mod type_sketch;

/// The fixed lattice of atomic types
pub mod type_lattice;

/// The main workhorse of the solver that describes a constraint set as a graph that admits type variables that satisfies the constraints.
pub mod constraint_graph;
