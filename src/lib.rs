//! # Type Constraint Generation by Abstract Interpretation

#![warn(missing_docs)]

mod analysis;
pub mod constraint_generation;
pub mod constraints;

#[cfg(test)]
pub(crate) mod test_utils;

pub mod util;

#[cfg(test)]
mod tests {}
