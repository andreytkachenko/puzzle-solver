//! This crate searches for the solutions to logic puzzles.
//! The puzzle rules are expressed as constraints.

pub mod constraint;

mod error;
mod linexpr;
mod puzzle;
mod ranges;

use num_rational::Rational32;
use std::ops;

pub use constraint::Constraint;
pub use error::Error;
pub use puzzle::Puzzle;
pub use puzzle::PuzzleSearch;
pub use linexpr::LinExpr;

/// A puzzle variable token.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct VarToken(usize);

/// The type of a puzzle variable's value (i.e. the candidate type).
pub type Val = i32;

/// The type of the coefficients in a linear expression.
pub type Coef = Rational32;


/// A result during a puzzle solution search (Err = contradiction).
pub type PsResult<T> = Result<T, Error>;

/// A dictionary mapping puzzle variables to the solution value.
#[derive(Debug)]
pub struct Solution {
    vars: Vec<Val>,
}

impl ops::Index<VarToken> for Solution {
    type Output = Val;
    fn index(&self, var: VarToken) -> &Val {
        let VarToken(idx) = var;
        &self.vars[idx]
    }
}
