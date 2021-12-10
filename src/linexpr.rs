//! Linear expressions.

use num_rational::{Ratio, Rational32};
use num_traits::{One, Signed, Zero};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::From;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

use crate::{Coef, VarToken};

/// A linear expression.
///
/// ```text
///   constant + coef1 * var1 + coef2 * var2 + ...
/// ```
#[derive(Clone)]
pub struct LinExpr {
    pub(crate) constant: Coef,

    // The non-zero coefficients in the linear expression.  If, after
    // some manipulations, the coefficient is 0, then it must be
    // removed from the map.
    pub(crate) coef: HashMap<VarToken, Coef>,
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

macro_rules! impl_commutative_op {
    ($LHS:ident + $RHS:ident) => {
        impl Add<$RHS> for $LHS {
            type Output = LinExpr;
            fn add(self, rhs: $RHS) -> Self::Output {
                rhs + self
            }
        }
    };
    ($LHS:ident * $RHS:ident) => {
        impl Mul<$RHS> for $LHS {
            type Output = LinExpr;
            fn mul(self, rhs: $RHS) -> Self::Output {
                rhs * self
            }
        }
    };
}

macro_rules! impl_subtract_op {
    ($LHS:ident - $RHS:ident) => {
        impl Sub<$RHS> for $LHS {
            type Output = LinExpr;
            fn sub(self, rhs: $RHS) -> Self::Output {
                self + (-rhs)
            }
        }
    };
}

pub trait IntoCoef: Zero {
    fn into_coef(self) -> Coef;
}

impl IntoCoef for i32 {
    fn into_coef(self) -> Coef {
        Ratio::from_integer(self)
    }
}

impl IntoCoef for Rational32 {
    fn into_coef(self) -> Coef {
        self
    }
}

/*--------------------------------------------------------------*/

impl<T: IntoCoef> From<T> for LinExpr {
    fn from(constant: T) -> Self {
        LinExpr {
            constant: constant.into_coef(),
            coef: HashMap::new(),
        }
    }
}

impl From<VarToken> for LinExpr {
    fn from(var: VarToken) -> Self {
        let mut coef = HashMap::new();
        coef.insert(var, Ratio::one());

        LinExpr {
            constant: Ratio::zero(),
            coef,
        }
    }
}

/*--------------------------------------------------------------*/
/* Var-Coef                                                     */
/*--------------------------------------------------------------*/

impl Neg for VarToken {
    type Output = LinExpr;
    fn neg(self) -> Self::Output {
        -LinExpr::from(self)
    }
}

impl<T: IntoCoef> Add<T> for VarToken {
    type Output = LinExpr;
    fn add(self, rhs: T) -> Self::Output {
        LinExpr::from(self) + rhs
    }
}

impl_commutative_op!(i32 + VarToken);
impl_commutative_op!(Rational32 + VarToken);

impl_subtract_op!(VarToken - i32);
impl_subtract_op!(i32 - VarToken);
impl_subtract_op!(VarToken - Rational32);
impl_subtract_op!(Rational32 - VarToken);

impl<T: IntoCoef> Mul<T> for VarToken {
    type Output = LinExpr;
    fn mul(self, rhs: T) -> Self::Output {
        LinExpr::from(self) * rhs
    }
}

impl_commutative_op!(i32 * VarToken);
impl_commutative_op!(Rational32 * VarToken);

/*--------------------------------------------------------------*/
/* Var-Var                                                      */
/*--------------------------------------------------------------*/

impl Add for VarToken {
    type Output = LinExpr;
    fn add(self, rhs: VarToken) -> Self::Output {
        LinExpr::from(self) + LinExpr::from(rhs)
    }
}

impl_subtract_op!(VarToken - VarToken);

/*--------------------------------------------------------------*/
/* Expr-Coef                                                    */
/*--------------------------------------------------------------*/

impl Neg for LinExpr {
    type Output = LinExpr;
    fn neg(self) -> Self::Output {
        -1 * self
    }
}

impl<T: IntoCoef> Add<T> for LinExpr {
    type Output = LinExpr;
    fn add(mut self, rhs: T) -> Self::Output {
        self.constant += rhs.into_coef();
        self
    }
}

impl_commutative_op!(i32 + LinExpr);
impl_commutative_op!(Rational32 + LinExpr);

impl_subtract_op!(LinExpr - i32);
impl_subtract_op!(i32 - LinExpr);
impl_subtract_op!(LinExpr - Rational32);
impl_subtract_op!(Rational32 - LinExpr);

impl<T: IntoCoef> Mul<T> for LinExpr {
    type Output = LinExpr;
    fn mul(mut self, rhs: T) -> Self::Output {
        if rhs.is_zero() {
            self.constant = Ratio::zero();
            self.coef = HashMap::new();
        } else {
            let rhs = rhs.into_coef();
            if rhs != Ratio::one() {
                self.constant *= rhs;
                for coef in self.coef.values_mut() {
                    *coef *= rhs;
                }
            }
        }

        self
    }
}

impl_commutative_op!(i32 * LinExpr);
impl_commutative_op!(Rational32 * LinExpr);

/*--------------------------------------------------------------*/
/* Expr-Var                                                     */
/*--------------------------------------------------------------*/

impl Add<VarToken> for LinExpr {
    type Output = LinExpr;
    fn add(self, rhs: VarToken) -> Self::Output {
        self + LinExpr::from(rhs)
    }
}

impl_commutative_op!(VarToken + LinExpr);

impl_subtract_op!(LinExpr - VarToken);
impl_subtract_op!(VarToken - LinExpr);

/*--------------------------------------------------------------*/
/* Expr-Expr                                                    */
/*--------------------------------------------------------------*/

impl Add for LinExpr {
    type Output = LinExpr;
    fn add(mut self, mut rhs: LinExpr) -> Self::Output {
        self.constant += rhs.constant;

        for (x2, a2) in rhs.coef.drain() {
            match self.coef.entry(x2) {
                Entry::Vacant(e) => {
                    e.insert(a2);
                }
                Entry::Occupied(mut e) => {
                    let new_coef = *e.get() + a2;
                    if new_coef.is_zero() {
                        e.remove();
                    } else {
                        *e.get_mut() = new_coef;
                    }
                }
            }
        }

        self
    }
}

impl_subtract_op!(LinExpr - LinExpr);

/*--------------------------------------------------------------*/

#[cfg(test)]
mod tests {
    use crate::Puzzle;
    use num_rational::Ratio;

    #[test]
    #[allow(clippy::identity_op, clippy::eq_op)]
    fn test_ops() {
        let mut puzzle = Puzzle::new();
        let x = puzzle.new_var(10..=10);
        let y = puzzle.new_var(10..=10);

        // expr = var + const;
        let _ = x + 1;
        let _ = x - 1;
        let _ = x * 1;
        let _ = x + Ratio::new(1, 2);
        let _ = x - Ratio::new(1, 2);
        let _ = x * Ratio::new(1, 2);

        // expr = const + var;
        let _ = 1 + x;
        let _ = 1 - x;
        let _ = 1 * x;
        let _ = Ratio::new(1, 2) + x;
        let _ = Ratio::new(1, 2) - x;
        let _ = Ratio::new(1, 2) * x;

        // expr = var + var;
        let _ = -x;
        let _ = x + y;
        let _ = x - y;

        // expr = expr + const;
        let _ = (x + y) + 1;
        let _ = (x + y) - 1;
        let _ = (x + y) * 1;
        let _ = (x + y) + Ratio::new(1, 2);
        let _ = (x + y) - Ratio::new(1, 2);
        let _ = (x + y) * Ratio::new(1, 2);

        // expr = const + expr;
        let _ = 1 + (x + y);
        let _ = 1 - (x + y);
        let _ = 1 * (x + y);
        let _ = Ratio::new(1, 2) + (x + y);
        let _ = Ratio::new(1, 2) - (x + y);
        let _ = Ratio::new(1, 2) * (x + y);

        // expr = expr + var;
        let _ = (x + 1) + y;
        let _ = (x + 1) - y;

        // expr = var + expr;
        let _ = x + (y + 1);
        let _ = x - (y + 1);

        // expr = expr + expr;
        let _ = -(x + y);
        let _ = (x + y) + (x + y);
        let _ = (x + y) - (x + y);
    }

    #[test]
    #[allow(clippy::erasing_op, clippy::eq_op)]
    fn test_coef_zero() {
        let mut puzzle = Puzzle::new();
        let x = puzzle.new_var(10..10);
        let y = puzzle.new_var(10..10);

        let expr = x * 0;
        assert_eq!(expr.coef.len(), 0);

        let expr = x - x;
        assert_eq!(expr.coef.len(), 0);

        let expr = (x + y) * 0;
        assert_eq!(expr.coef.len(), 0);

        let expr = (x + y) - (x + y);
        assert_eq!(expr.coef.len(), 0);
    }
}
