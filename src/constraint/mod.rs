//! Constraint trait, and some common constraints.
//!
//! Note that all puzzle states visited during the solution search
//! share the same set of constraint objects.  This means that you
//! cannot store additional information about the state (e.g. caches)
//! in the constraint to reuse later.

use std::fmt::Debug;
use std::rc::Rc;

use crate::{PsResult, PuzzleSearch, Val, VarToken};

/// Constraint trait.
pub trait Constraint: Debug {
    /// An iterator over the variables that are involved in the constraint.
    fn vars(&self) -> Box<dyn Iterator<Item = &'_ VarToken> + '_>;

    /// Applied after a variable has been assigned.
    fn propagate(&self, _search: &mut PuzzleSearch, _var: VarToken, _val: Val) -> PsResult<()>; 

    /// Applied after a variable's candidates has been modified.
    fn on_updated(&self, _search: &mut PuzzleSearch) -> PsResult<()> {
        Ok(())
    }

    /// Substitute the "from" variable with the "to" variable.
    ///
    /// Returns a new constraint with all instances of "from" replaced
    /// with "to", or Err if a contradiction was found.
    fn substitute(&self, from: VarToken, to: VarToken) -> PsResult<Rc<dyn Constraint>>;
}

pub use self::alldifferent::AllDifferent;
pub use self::equality::Equality;
pub use self::unify::Unify;

mod alldifferent;
mod equality;
mod unify;
