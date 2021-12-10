//! The puzzle's state and rules.

use bit_set::BitSet;
use std::cell::Cell;
use std::collections::BTreeSet;
use std::fmt;
use std::iter;
use std::mem;
use std::ops;
use std::ops::Bound;
use std::ops::RangeBounds;
use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};
use std::rc::Rc;

use crate::constraint;
use crate::linexpr::LinExpr;
use crate::ranges::Ranges;
use crate::Error;
use crate::{Constraint, PsResult, Solution, Val, VarToken};

/// A collection of candidates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Candidates {
    Value(Val),             // A variable set to its initial value.
    Set(Rc<BTreeSet<Val>>), // A variable with a list of candidates.
    Range(Ranges),          // A variable with candidate ranges.
}

impl From<Val> for Candidates {
    fn from(val: Val) -> Self {
        Candidates::Value(val)
    }
}

impl From<&[Val]> for Candidates {
    fn from(set: &[Val]) -> Self {
        Candidates::Set(Rc::new(set.iter().copied().collect()))
    }
}

impl <const N: usize> From<&[Val; N]> for Candidates {
    fn from(set: &[Val; N]) -> Self {
        Candidates::Set(Rc::new(set.iter().copied().collect()))
    }
}

impl <const N: usize> From<[Val; N]> for Candidates {
    fn from(set: [Val; N]) -> Self {
        Candidates::Set(Rc::new(set.into_iter().collect()))
    }
}

impl From<Vec<Val>> for Candidates {
    fn from(set: Vec<Val>) -> Self {
        Candidates::Set(Rc::new(set.into_iter().collect()))
    }
}

impl From<Range<Val>> for Candidates {
    fn from(range: Range<Val>) -> Self {
        Candidates::Range(range.into())
    }
}

impl From<RangeFrom<Val>> for Candidates {
    fn from(range: RangeFrom<Val>) -> Self {
        Candidates::Range(range.into())
    }
}

impl From<RangeTo<Val>> for Candidates {
    fn from(range: RangeTo<Val>) -> Self {
        Candidates::Range(range.into())
    }
}

impl From<RangeInclusive<Val>> for Candidates {
    fn from(range: RangeInclusive<Val>) -> Self {
        Candidates::Range(range.into())
    }
}

impl From<RangeToInclusive<Val>> for Candidates {
    fn from(range: RangeToInclusive<Val>) -> Self {
        Candidates::Range(range.into())
    }
}

impl From<RangeFull> for Candidates {
    fn from(range: RangeFull) -> Self {
        Candidates::Range(range.into())
    }
}

impl From<(Bound<Val>, Bound<Val>)> for Candidates {
    fn from(range: (Bound<Val>, Bound<Val>)) -> Self {
        Candidates::Range(range.into())
    }
}

/// The state of a variable during the solution search.
#[derive(Clone, Debug)]
enum VarState {
    Assigned(Val),
    Unassigned(Candidates),
    Unified(VarToken),
}

/// The puzzle to be solved.
pub struct Puzzle {
    // The number of variables in the puzzle.
    num_vars: usize,

    // The number of guesses to solve the puzzle.
    num_guesses: Cell<u32>,

    // The list of candidates for each variable.
    candidates: Vec<Candidates>,

    // The list of puzzle constraints.
    constraints: Vec<Rc<dyn Constraint>>,
}

/// The puzzle constraints, and the variables that wake them up.
struct PuzzleConstraints {
    // The list of puzzle constraints, possibly with variables
    // substituted out.
    constraints: Vec<Rc<dyn Constraint>>,

    // The list of constraints that each variable affects.  These will
    // be woken up when the variable's candidates are changed.
    wake: Vec<BitSet>,
}

/// Intermediate puzzle search state.
#[derive(Clone)]
pub struct PuzzleSearch<'a> {
    puzzle: &'a Puzzle,
    constraints: Rc<PuzzleConstraints>,
    vars: Vec<VarState>,

    // The list of constraints that need to be re-evaluated.
    wake: BitSet,
}

/*--------------------------------------------------------------*/

impl Candidates {
    /// Count the number of candidates for a variable.
    fn len(&self) -> usize {
        match self {
            Candidates::Value(_) => 1,
            Candidates::Set(ref rc) => rc.len(),
            Candidates::Range(rc) => rc.len(),
        }
    }

    /// Get an iterator over all of the candidates of a variable.
    fn iter(&self) -> Box<dyn Iterator<Item = Val> + '_> {
        match self {
            Candidates::Value(val) => Box::new(iter::once(*val)),
            Candidates::Set(ref rc) => Box::new(rc.iter().cloned()),
            Candidates::Range(range) => Box::new(range.iter()),
        }
    }
}

/*--------------------------------------------------------------*/

impl Puzzle {
    /// Allocate a new puzzle.
    ///
    /// # Examples
    ///
    /// ```
    /// puzzle_solver::Puzzle::new();
    /// ```
    pub fn new() -> Self {
        Puzzle {
            num_vars: 0,
            num_guesses: Cell::new(0),
            candidates: Vec::new(),
            constraints: Vec::new(),
        }
    }

    pub fn new_var<C: Into<Candidates>>(&mut self, candidates: C) -> VarToken {
        let var = VarToken(self.num_vars);
        self.num_vars += 1;
        self.candidates.push(candidates.into());
        var
    }

    /// Allocate a 1d vector of puzzle variables, each initialised to
    /// have the same set of potential candidates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// send_more_money.new_vars(8, &[0,1,2,3,4,5,6,7,8,9]);
    /// ```
    pub fn new_vars<C: Into<Candidates> + Clone>(&mut self, n: usize, candidates: C) -> Vec<VarToken> {
        let mut vars = Vec::with_capacity(n);
        for _ in 0..n {
            vars.push(self.new_var(candidates.clone()));
        }
        vars
    }

    /// Allocate a 2d array of puzzle variables, each initialised to
    /// have the same set of potential candidates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut magic_square = puzzle_solver::Puzzle::new();
    /// magic_square.new_vars_2d(3, 3, &[1,2,3,4,5,6,7,8,9]);
    /// ```
    pub fn new_vars_2d<C: Into<Candidates> + Clone>(
        self: &mut Puzzle,
        width: usize,
        height: usize,
        candidates: C,
    ) -> Vec<Vec<VarToken>> {
        let mut vars = Vec::with_capacity(height);
        for _ in 0..height {
            vars.push(self.new_vars(width, candidates.clone()));
        }
        vars
    }

    /// Set a variable to a known value.
    ///
    /// This is useful when the variable is given as part of the
    /// problem.  After this operation, any subsequent attempts to set
    /// the value will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut magic_square = puzzle_solver::Puzzle::new();
    /// let vars = magic_square.new_vars_2d(3, 3,
    ///         &[1,2,3,4,5,6,7,8,9]);
    ///
    /// magic_square.set_value(vars[1][1], 5);
    /// ```
    pub fn set_value(&mut self, var: VarToken, value: Val) {
        let VarToken(idx) = var;

        if let Candidates::Value(val) = self.candidates[idx] {
            if val != value {
                panic!("attempt to set fixed variable");
            }
        }

        self.candidates[idx] = Candidates::Value(value);
    }

    /// Add candidates to a variable.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// for _ in 0..9 {
    ///     let var = send_more_money.new_var([]);
    ///     send_more_money.insert_candidates(var, &[0,1,2,3,4,5,6,7,8,9]);
    /// }
    /// ```
    pub fn insert_candidates(&mut self, var: VarToken, candidates: &[Val]) {
        let VarToken(idx) = var;

        match self.candidates[idx] {
            Candidates::Value(_) => panic!("attempt to set fixed variable"),
            Candidates::Range(_) => panic!("attempt to insert candidates into range"),
            Candidates::Set(_) => (),
        }

        if let Candidates::Set(ref mut rc) = self.candidates[idx] {
            let cs = Rc::get_mut(rc).expect("unique");
            cs.extend(candidates);
        }
    }

    /// Remove candidates from a variable.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// let vars = send_more_money.new_vars(8,
    ///         &[0,1,2,3,4,5,6,7,8,9]);
    ///
    /// let s = vars[0];
    /// let m = vars[4];
    /// send_more_money.remove_candidates(s, &[0]);
    /// send_more_money.remove_candidates(m, &[0]);
    /// ```
    pub fn remove_candidates(&mut self, var: VarToken, candidates: &[Val]) {
        let VarToken(idx) = var;

        match self.candidates[idx] {
            Candidates::Value(_) => panic!("attempt to set fixed variable"),
            Candidates::Range(_) => panic!("attempt to remove candidates from range"),
            Candidates::Set(ref mut rc) => {
                let cs = Rc::get_mut(rc).expect("unique");
                for c in candidates.iter() {
                    cs.remove(c);
                }
            }
        }
    }

    /// Set the variable's candidates to the intersection with the
    /// given list.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// let vars = send_more_money.new_vars(8,
    ///         &[0,1,2,3,4,5,6,7,8,9]);
    ///
    /// let m = vars[4];
    /// send_more_money.intersect_candidates(m, &[0,1]);
    /// ```
    pub fn intersect_candidates(&mut self, var: VarToken, candidates: &[Val]) {
        let VarToken(idx) = var;

        match self.candidates[idx] {
            Candidates::Value(_) => panic!("attempt to set fixed variable"),
            Candidates::Range(_) => panic!("attempt to intersect candidates on the range"),
            Candidates::Set(ref mut rc) => {
                let cs = Rc::get_mut(rc).expect("unique");
                let mut set = BTreeSet::new();
                set.extend(candidates);
                *cs = cs.intersection(&set).cloned().collect();
            }
        }
    }

    ///
    /// Insert range
    ///
    ///
    pub fn insert_range<R: RangeBounds<Val>>(&mut self, var: VarToken, range: R) {
        let VarToken(idx) = var;

        match self.candidates[idx] {
            Candidates::Value(_) => panic!("attempt to set fixed variable"),
            Candidates::Range(ref mut r) => {
                r.insert(range.start_bound().cloned(), range.end_bound().cloned());
            }
            Candidates::Set(_) => panic!("attempt to insert range on set"),
        }
    }

    /// Add a constraint to the puzzle solution.
    pub fn add_constraint<T>(&mut self, constraint: T)
    where
        T: Constraint + 'static,
    {
        self.constraints.push(Rc::new(constraint));
    }

    /// Add an All Different constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// let vars = send_more_money.new_vars(8,
    ///         &[0,1,2,3,4,5,6,7,8,9]);
    ///
    /// send_more_money.all_different(&vars);
    /// ```
    pub fn all_different<'a, I>(&mut self, vars: I)
    where
        I: IntoIterator<Item = &'a VarToken>,
    {
        self.add_constraint(constraint::AllDifferent::new(vars));
    }

    /// Add an Equality constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut magic_square = puzzle_solver::Puzzle::new();
    /// let vars = magic_square.new_vars_2d(3, 3,
    ///         &[1,2,3,4,5,6,7,8,9]);
    ///
    /// magic_square.equals(vars[0][0] + vars[0][1] + vars[0][2], 15);
    /// ```
    pub fn equals<L, R>(&mut self, lhs: L, rhs: R)
    where
        L: Into<LinExpr>,
        R: Into<LinExpr>,
    {
        self.add_constraint(constraint::Equality::new(lhs.into() - rhs.into()));
    }

    /// Add a Unify constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// let carry = send_more_money.new_vars(4, &[0,1]);
    /// let vars = send_more_money.new_vars(8,
    ///         &[0,1,2,3,4,5,6,7,8,9]);
    ///
    /// let m = vars[4];
    /// send_more_money.unify(m, carry[3]);
    /// ```
    pub fn unify(&mut self, var1: VarToken, var2: VarToken) {
        self.add_constraint(constraint::Unify::new(var1, var2));
    }

    /// Find any solution to the given puzzle.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut puzzle = puzzle_solver::Puzzle::new();
    /// puzzle.new_var(&[1,2]);
    /// puzzle.new_var(&[3,4]);
    ///
    /// let solution = puzzle.solve_any();
    /// assert!(solution.is_some());
    /// ```
    pub fn solve_any(&mut self) -> Option<Solution> {
        let mut solutions = Vec::with_capacity(1);

        self.num_guesses.set(0);
        if self.num_vars > 0 {
            let mut search = PuzzleSearch::new(self);
            search.solve(1, &mut solutions);
        }

        solutions.pop()
    }

    /// Find the solution to the given puzzle, verifying that it is
    /// unique.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut puzzle = puzzle_solver::Puzzle::new();
    /// puzzle.new_var(&[1,2]);
    /// puzzle.new_var(&[3,4]);
    ///
    /// let solution = puzzle.solve_unique();
    /// assert!(solution.is_none());
    /// ```
    pub fn solve_unique(&mut self) -> Option<Solution> {
        self.num_guesses.set(0);
        if self.num_vars > 0 {
            let mut search = PuzzleSearch::new(self);
            let mut solutions = Vec::with_capacity(2);
            search.solve(2, &mut solutions);
            if solutions.len() == 1 {
                return solutions.pop();
            }
        }

        None
    }

    /// Find all solutions to the given puzzle.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut puzzle = puzzle_solver::Puzzle::new();
    /// puzzle.new_var(&[1,2]);
    /// puzzle.new_var(&[3,4]);
    ///
    /// let solutions = puzzle.solve_all();
    /// assert_eq!(solutions.len(), 4);
    /// ```
    pub fn solve_all(&mut self) -> Vec<Solution> {
        let mut solutions = Vec::new();

        self.num_guesses.set(0);
        if self.num_vars > 0 {
            let mut search = PuzzleSearch::new(self);
            search.solve(::std::usize::MAX, &mut solutions);
        }

        solutions
    }

    /// Take any obvious non-choices, using the constraints to
    /// eliminate candidates.  Stops when it must start guessing.
    /// Primarily for testing.
    ///
    /// Returns the intermediate puzzle search state, or None if a
    /// contradiction was found.
    pub fn step(&mut self) -> Option<PuzzleSearch> {
        if self.num_vars > 0 {
            let mut search = PuzzleSearch::new(self);
            if search.constrain().is_ok() {
                return Some(search);
            }
        }

        None
    }

    /// Get the number of guesses taken to solve the last puzzle.
    pub fn num_guesses(&self) -> u32 {
        self.num_guesses.get()
    }
}

impl Default for Puzzle {
    fn default() -> Self {
        Self::new()
    }
}

/*--------------------------------------------------------------*/

impl PuzzleConstraints {
    /// Allocate a new puzzle constraint container.
    fn new(puzzle: &Puzzle) -> Self {
        let wake = Self::init_wake(&puzzle.constraints, puzzle.num_vars);
        PuzzleConstraints {
            constraints: puzzle.constraints.clone(),
            wake,
        }
    }

    /// Create a new puzzle constraint container reflecting the
    /// substitution of "from" with "to".
    fn substitute(&self, from: VarToken, to: VarToken) -> PsResult<Self> {
        let VarToken(idx) = from;
        let mut new_constraints = self.constraints.clone();

        for cidx in self.wake[idx].iter() {
            let rc = self.constraints[cidx].substitute(from, to)?;
            new_constraints[cidx] = rc;
        }

        let wake = Self::init_wake(&new_constraints, self.wake.len());
        Ok(PuzzleConstraints {
            constraints: new_constraints,
            wake,
        })
    }

    /// Determine which variables wake up which constraints.
    fn init_wake(constraints: &[Rc<dyn Constraint>], num_vars: usize) -> Vec<BitSet> {
        let mut wake = vec![BitSet::new(); num_vars];
        for (cidx, constraint) in constraints.iter().enumerate() {
            for &VarToken(idx) in constraint.vars() {
                wake[idx].insert(cidx);
            }
        }

        wake
    }
}

/*--------------------------------------------------------------*/

impl<'a> PuzzleSearch<'a> {
    /// Allocate a new puzzle searcher.
    fn new(puzzle: &'a Puzzle) -> Self {
        let constraints = PuzzleConstraints::new(puzzle);
        let vars = puzzle
            .candidates
            .iter()
            .map(|cs| VarState::Unassigned(cs.clone()))
            .collect();
        let mut wake = BitSet::new();

        for cidx in 0..constraints.constraints.len() {
            wake.insert(cidx);
        }

        PuzzleSearch {
            puzzle,
            constraints: Rc::new(constraints),
            vars,
            wake,
        }
    }

    /// Check if the variable has been assigned to a value.
    pub fn is_assigned(&self, var: VarToken) -> bool {
        let VarToken(idx) = var;
        match &self.vars[idx] {
            VarState::Assigned(_) => true,
            VarState::Unassigned(_) => false,
            VarState::Unified(other) => self.is_assigned(*other),
        }
    }

    /// Get the value assigned to a variable, or None.
    ///
    /// This should be used if the variable may potentially be
    /// unassigned.  For example, when implementing constraints.
    pub fn get_assigned(&self, var: VarToken) -> Option<Val> {
        let VarToken(idx) = var;
        match &self.vars[idx] {
            VarState::Assigned(val) => Some(*val),
            VarState::Unassigned(_) => None,
            VarState::Unified(other) => self.get_assigned(*other),
        }
    }

    /// Get an iterator over the candidates to an unassigned variable.
    pub fn get_unassigned(&self, var: VarToken) -> Box<dyn Iterator<Item = Val> + '_> {
        let VarToken(idx) = var;
        match &self.vars[idx] {
            VarState::Assigned(_) => Box::new(iter::empty()),
            VarState::Unassigned(ref cs) => cs.iter(),
            VarState::Unified(other) => self.get_unassigned(*other),
        }
    }

    /// Get the minimum and maximum values for variable.
    pub fn get_min_max(&self, var: VarToken) -> PsResult<(Val, Val)> {
        let VarToken(idx) = var;
        match &self.vars[idx] {
            VarState::Assigned(val) => Ok((*val, *val)),
            VarState::Unassigned(ref cs) => match cs {
                Candidates::Value(val) => Ok((*val, *val)),
                Candidates::Range(r) => r.get_bounds().ok_or(Error::Default),
                Candidates::Set(ref rc) => rc
                    .iter()
                    .cloned()
                    .min()
                    .into_iter()
                    .zip(rc.iter().cloned().max())
                    .next()
                    .ok_or(Error::Default),
            },
            VarState::Unified(other) => self.get_min_max(*other),
        }
    }

    /// Set a variable to a value.
    pub fn set_candidate(&mut self, var: VarToken, val: Val) -> PsResult<()> {
        let VarToken(idx) = var;

        match self.vars[idx] {
            VarState::Assigned(v) => bool_to_result(v == val),
            VarState::Unassigned(ref mut cs) => match cs {
                Candidates::Value(v) => bool_to_result(*v == val),
                Candidates::Range(ref mut r) => {
                    if r.contains(val) {
                        *r = (val..=val).into();
                        self.wake.union_with(&self.constraints.wake[idx]);

                        Ok(())
                    } else {
                        Err(Error::Default)
                    }
                }
                Candidates::Set(rc) => {
                    if rc.contains(&val) {
                        let set = Rc::make_mut(rc);
                        set.clear();
                        set.insert(val);
                        self.wake.union_with(&self.constraints.wake[idx]);
                        Ok(())
                    } else {
                        Err(Error::Default)
                    }
                }
            },
            VarState::Unified(other) => self.set_candidate(other, val),
        }
    }

    /// Remove a single candidate from a variable.
    pub fn remove_candidate(&mut self, var: VarToken, val: Val) -> PsResult<()> {
        let VarToken(idx) = var;

        match self.vars[idx] {
            VarState::Assigned(v) => bool_to_result(v != val),
            VarState::Unassigned(ref mut cs) => match cs {
                Candidates::Value(v) => bool_to_result(*v != val),
                Candidates::Range(r) => {
                    if r.contains(val) {
                        r.remove(val..=val);
                        self.wake.union_with(&self.constraints.wake[idx]);
                    }

                    bool_to_result(!r.is_empty())
                }
                Candidates::Set(rc) => {
                    if rc.contains(&val) {
                        let set = Rc::make_mut(rc);
                        set.remove(&val);
                        self.wake.union_with(&self.constraints.wake[idx]);
                    }
                    bool_to_result(!rc.is_empty())
                }
            },
            VarState::Unified(other) => self.remove_candidate(other, val),
        }
    }

    /// Bound an variable to the given range.
    pub fn bound_candidate_range(
        &mut self,
        var: VarToken,
        min: Val,
        max: Val,
    ) -> PsResult<(Val, Val)> {
        let VarToken(idx) = var;

        match self.vars[idx] {
            VarState::Assigned(v) => {
                if min <= v && v <= max {
                    Ok((v, v))
                } else {
                    Err(Error::Default)
                }
            }

            VarState::Unassigned(ref mut cs) => match cs {
                Candidates::Value(v) => {
                    if min <= *v && *v <= max {
                        Ok((*v, *v))
                    } else {
                        Err(Error::Default)
                    }
                }

                Candidates::Range(ref mut r) => {
                    if max < min {
                        return Err(Error::Default);
                    }

                    r.intersection(min..=max);

                    self.wake.union_with(&self.constraints.wake[idx]);

                    r.get_bounds().ok_or(Error::Default)
                }

                Candidates::Set(rc) => {
                    let &curr_min = rc.iter().min().expect("candidates");
                    let &curr_max = rc.iter().max().expect("candidates");

                    if curr_min < min || max < curr_max {
                        let set = Rc::make_mut(rc);
                        *set = set
                            .iter()
                            .filter(|&val| min <= *val && *val <= max)
                            .cloned()
                            .collect();
                        self.wake.union_with(&self.constraints.wake[idx]);
                        rc.iter()
                            .cloned()
                            .min()
                            .into_iter()
                            .zip(rc.iter().cloned().max())
                            .next()
                            .ok_or(Error::Default)
                    } else {
                        Ok((curr_min, curr_max))
                    }
                }
            },

            VarState::Unified(other) => self.bound_candidate_range(other, min, max),
        }
    }

    /// Solve the puzzle, finding up to count solutions.
    fn solve(&mut self, count: usize, solutions: &mut Vec<Solution>) {
        if self.constrain().is_err() {
            return;
        }

        let next_unassigned = self
            .vars
            .iter()
            .enumerate()
            .min_by_key(|&(_, vs)| match vs {
                VarState::Unassigned(ref cs) => cs.len(),
                _ => ::std::usize::MAX,
            });

        if let Some((idx, &VarState::Unassigned(ref cs))) = next_unassigned {
            if cs.len() == 0 {
                // Contradiction.
                return;
            }

            for val in cs.iter() {
                let num_guesses = self.puzzle.num_guesses.get() + 1;
                self.puzzle.num_guesses.set(num_guesses);

                let mut new = self.clone();
                if new.assign(idx, val).is_err() {
                    continue;
                }

                new.solve(count, solutions);
                if solutions.len() >= count {
                    // Reached desired number of solutions.
                    return;
                }
            }
        } else {
            // No unassigned variables remaining.
            let vars = (0..self.puzzle.num_vars)
                .map(|idx| self[VarToken(idx)])
                .collect();
            solutions.push(Solution { vars });
        }
    }

    /// Assign a variable (given by index) to a value.
    fn assign(&mut self, idx: usize, val: Val) -> PsResult<()> {
        let var = VarToken(idx);
        self.vars[idx] = VarState::Assigned(val);
        self.wake.union_with(&self.constraints.wake[idx]);

        for cidx in 0..self.constraints.constraints.len() {
            if self.constraints.wake[idx].contains(cidx) {
                let constraint = self.constraints.constraints[cidx].clone();
                constraint.propagate(self, var, val)?;
            }
        }

        Ok(())
    }

    /// Take any obvious non-choices, using the constraints to
    /// eliminate candidates.  Stops when it must start guessing.
    fn constrain(&mut self) -> PsResult<()> {
        while !self.wake.is_empty() {
            // "Gimme" phase:
            // - abort if any variables with 0 candidates,
            // - assign variables with only 1 candidate.
            // - repeat until no more gimmes found.
            let cycle = self.vars.len();
            let mut idx = 0;
            let mut last_gimme = cycle - 1;
            loop {
                let gimme = match self.vars[idx] {
                    VarState::Assigned(_) => None,
                    VarState::Unassigned(ref cs) => match cs.len() {
                        0 => return Err(Error::Default),
                        1 => cs.iter().next(),
                        _ => None,
                    },
                    VarState::Unified(_) => None,
                };

                if let Some(val) = gimme {
                    self.assign(idx, val)?;
                    last_gimme = idx;
                } else if idx == last_gimme {
                    break;
                }

                idx = if idx + 1 >= cycle { 0 } else { idx + 1 };
            }

            // Apply constraints.
            if !self.wake.is_empty() {
                let wake = mem::replace(&mut self.wake, BitSet::new());
                for cidx in wake.iter() {
                    let constraint = self.constraints.constraints[cidx].clone();
                    constraint.on_updated(self)?;
                }
            }
        }

        Ok(())
    }

    /// Unify the "from" variable with the "to" variable.
    pub fn unify(&mut self, from: VarToken, to: VarToken) -> PsResult<()> {
        if from == to {
            return Ok(());
        }

        // Some preliminary checks, and maybe swap "from" and "to" in
        // order to simplify our logic.
        let (from, to) = {
            let VarToken(search) = from;
            let VarToken(replace) = to;
            match (&self.vars[search], &self.vars[replace]) {
                (&VarState::Assigned(val1), &VarState::Assigned(val2)) => {
                    return bool_to_result(val1 == val2)
                }

                // Unified variables should have been substituted out previously.
                (&VarState::Unified(_), _) | (_, &VarState::Unified(_)) => {
                    panic!("internal representation corrupt")
                }

                (&VarState::Unassigned(_), &VarState::Assigned(_)) => (to, from),

                (&VarState::Assigned(_), &VarState::Unassigned(_))
                | (&VarState::Unassigned(_), &VarState::Unassigned(_)) => (from, to),
            }
        };

        let VarToken(search) = from;
        let VarToken(replace) = to;

        // Create new constraints to reflect the unification.
        let new_constraints = self.constraints.substitute(from, to)?;
        self.constraints = Rc::new(new_constraints);
        self.wake.union_with(&self.constraints.wake[replace]);
        assert!(self.constraints.wake[search].is_empty());

        // Take intersection of the candidates.
        if let VarState::Assigned(val) = self.vars[search] {
            self.set_candidate(to, val)?;
        } else if let (
            VarState::Unassigned(Candidates::Set(ref mut rc1)),
            VarState::Unassigned(Candidates::Set(ref mut rc2)),
        ) = get_two_mut(&mut self.vars, search, replace)
        {
            *rc2 = Rc::new(rc2.intersection(rc1).cloned().collect());
            if rc2.is_empty() {
                return Err(Error::Default);
            }
        }

        self.vars[search] = VarState::Unified(to);
        Ok(())
    }
}

impl fmt::Debug for PuzzleSearch<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "PuzzleSearch={{")?;
        for (idx, var) in self.vars.iter().enumerate() {
            writeln!(f)?;

            match var {
                VarState::Assigned(val) => {
                    write!(f, "  var {}: {}", idx, val)?;
                }
                VarState::Unassigned(ref cs) => {
                    write!(f, "  var {}:", idx)?;
                    for val in cs.iter() {
                        write!(f, " {}", val)?;
                    }
                }
                VarState::Unified(VarToken(other)) => {
                    write!(f, "  var {}: var {}", idx, other)?;
                }
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl ops::Index<VarToken> for PuzzleSearch<'_> {
    type Output = Val;

    /// Get the value assigned to a variable.
    ///
    /// # Panics
    ///
    /// Panics if the variable has not been assigned.
    fn index(&self, var: VarToken) -> &Val {
        let VarToken(idx) = var;
        match self.vars[idx] {
            VarState::Assigned(ref val) => val,
            VarState::Unassigned(_) => panic!("unassigned"),
            VarState::Unified(other) => &self[other],
        }
    }
}

fn bool_to_result(cond: bool) -> PsResult<()> {
    if cond {
        Ok(())
    } else {
        Err(Error::Default)
    }
}

fn get_two_mut<T>(slice: &mut [T], a: usize, b: usize) -> (&mut T, &mut T) {
    assert!(a != b);
    if a < b {
        let (l, r) = slice.split_at_mut(b);
        (&mut l[a], &mut r[0])
    } else {
        let (l, r) = slice.split_at_mut(a);
        (&mut r[0], &mut l[b])
    }
}

#[cfg(test)]
mod tests {
    use crate::Puzzle;

    #[test]
    fn test_no_vars() {
        let mut sys = Puzzle::new();
        sys.solve_any();
        sys.solve_unique();
        sys.solve_all();
        sys.step();
    }
}
