//! The puzzle's state and rules.

use std::collections::BTreeSet;
use std::rc::Rc;

use ::{Val,VarToken};

/// A collection of candidates.
#[derive(Clone,Debug,Eq,PartialEq)]
enum Candidates {
    None,                       // A variable with no candidates.
    Value(Val),                 // A variable set to its initial value.
    Set(Rc<BTreeSet<Val>>),     // A variable with a list of candidates.
}

/// The puzzle to be solved.
pub struct Puzzle {
    // The number of variables in the puzzle.
    num_vars: usize,

    // The list of candidates for each variable.
    candidates: Vec<Candidates>,
}

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
            candidates: Vec::new(),
        }
    }

    /// Allocate a new puzzle variable, without inserting any
    /// candidates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut puzzle = puzzle_solver::Puzzle::new();
    /// puzzle.new_var();
    /// ```
    pub fn new_var(&mut self) -> VarToken {
        let var = VarToken(self.num_vars);
        self.num_vars = self.num_vars + 1;
        self.candidates.push(Candidates::None);
        var
    }

    /// Allocate a new puzzle variable, initialising it with potential
    /// candidates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// send_more_money.new_var_with_candidates(&[0,1,2,3,4,5,6,7,8,9]);
    /// ```
    pub fn new_var_with_candidates(&mut self, candidates: &[Val]) -> VarToken {
        let var = self.new_var();
        self.insert_candidates(var, candidates);
        var
    }

    /// Allocate a 1d vector of puzzle variables, each initialised to
    /// have the same set of potential candidates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// send_more_money.new_vars_with_candidates_1d(8, &[0,1,2,3,4,5,6,7,8,9]);
    /// ```
    pub fn new_vars_with_candidates_1d(&mut self, n: usize, candidates: &[Val])
            -> Vec<VarToken> {
        let mut vars = Vec::with_capacity(n);
        for _ in 0..n {
            vars.push(self.new_var_with_candidates(candidates));
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
    /// magic_square.new_vars_with_candidates_2d(3, 3, &[1,2,3,4,5,6,7,8,9]);
    /// ```
    pub fn new_vars_with_candidates_2d(self: &mut Puzzle,
            width: usize, height: usize, candidates: &[Val])
            -> Vec<Vec<VarToken>> {
        let mut vars = Vec::with_capacity(height);
        for _ in 0..height {
            vars.push(self.new_vars_with_candidates_1d(width, candidates));
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
    /// let vars = magic_square.new_vars_with_candidates_2d(3, 3,
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
    ///     let var = send_more_money.new_var();
    ///     send_more_money.insert_candidates(var, &[0,1,2,3,4,5,6,7,8,9]);
    /// }
    /// ```
    pub fn insert_candidates(&mut self, var: VarToken, candidates: &[Val]) {
        let VarToken(idx) = var;

        match &self.candidates[idx] {
            &Candidates::Value(_) =>
                panic!("attempt to set fixed variable"),

            &Candidates::None => {
                self.candidates[idx] = Candidates::Set(Rc::new(BTreeSet::new()));
            },

            &Candidates::Set(_) => (),
        }

        // Why you dumb Rust?
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
    /// let vars = send_more_money.new_vars_with_candidates_1d(8,
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
            Candidates::Value(_) =>
                panic!("attempt to set fixed variable"),

            Candidates::None => (),

            Candidates::Set(ref mut rc) => {
                let cs = Rc::get_mut(rc).expect("unique");
                for c in candidates.iter() {
                    cs.remove(c);
                }
            },
        }
    }

    /// Set the variable's candidates to the intersection with the
    /// given list.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut send_more_money = puzzle_solver::Puzzle::new();
    /// let vars = send_more_money.new_vars_with_candidates_1d(8,
    ///         &[0,1,2,3,4,5,6,7,8,9]);
    ///
    /// let m = vars[4];
    /// send_more_money.intersect_candidates(m, &[0,1]);
    /// ```
    pub fn intersect_candidates(&mut self, var: VarToken, candidates: &[Val]) {
        let VarToken(idx) = var;

        match self.candidates[idx] {
            Candidates::Value(_) =>
                panic!("attempt to set fixed variable"),

            Candidates::None => (),

            Candidates::Set(ref mut rc) => {
                let cs = Rc::get_mut(rc).expect("unique");
                let mut set = BTreeSet::new();
                set.extend(candidates);
                *cs = cs.intersection(&set).cloned().collect();
            },
        }
    }
}