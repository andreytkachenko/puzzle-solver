//! This crate searches for the solutions to logic puzzles.
//! The puzzle rules are expressed as constraints.

pub mod constraint;

mod error;
mod linexpr;
mod puzzle;
mod ranges;

use core::fmt;
use num_rational::Rational32;
use num_traits::Signed;
use std::collections::HashMap;
use std::ops;

pub use constraint::Constraint;
pub use error::Error;
pub use puzzle::Puzzle;
pub use puzzle::PuzzleSearch;

/// A puzzle variable token.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct VarToken(usize);

/// The type of a puzzle variable's value (i.e. the candidate type).
pub type Val = i32;

/// The type of the coefficients in a linear expression.
pub type Coef = Rational32;

/// A linear expression.
///
/// ```text
///   constant + coef1 * var1 + coef2 * var2 + ...
/// ```
#[derive(Clone)]
pub struct LinExpr {
    constant: Coef,

    // The non-zero coefficients in the linear expression.  If, after
    // some manipulations, the coefficient is 0, then it must be
    // removed from the map.
    coef: HashMap<VarToken, Coef>,
}

impl fmt::Display for LinExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.constant)?;

        for (tok, coef) in self.coef.iter() {
            if coef.is_negative() {
                if coef.abs() == Rational32::from_integer(1) {
                    write!(f, " - x{}", tok.0)?;
                } else {
                    write!(f, " - {} * x{}", coef.abs(), tok.0)?;
                }
            } else if coef.abs() == Rational32::from_integer(1) {
                write!(f, " + x{}", tok.0)?;
            } else {
                write!(f, " + {} * x{}", coef, tok.0)?;
            }
        }

        Ok(())
    }
}

impl fmt::Debug for LinExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LinExpr {{ {} }}", self)
    }
}

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
