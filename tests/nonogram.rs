//! Nonogram (A.K.A. Hanjie, Picross).
//!
//! https://en.wikipedia.org/wiki/Nonogram

extern crate puzzle_solver;

use puzzle_solver::*;
use std::collections::HashMap;
use std::rc::Rc;

const WIDTH: usize = 20;
const HEIGHT: usize = 20;
type Board = [[Val; WIDTH]; HEIGHT];

/*--------------------------------------------------------------*/

const FLAG_OFF: Val = 1;
const FLAG_ON: Val = 2;
const FLAG_UNKNOWN: Val = 4;

#[derive(Debug)]
struct Nonogram {
    vars: Vec<VarToken>,
    rule: Vec<usize>,
}

#[derive(Clone, Copy)]
enum AutoFillResult {
    // Too many solutions, no need to find any more
    SearchEnded,

    // Descendant found a solution.
    // Backtrack and look for other solutions.
    SolutionFound,

    // Some earlier choices lead to a conflict.
    // Backtrack and look for other solutions.
    Conflict,
}

impl Nonogram {
    fn new(vars: &[VarToken], rule: &[usize]) -> Self {
        Nonogram {
            vars: vars.to_vec(),
            rule: rule.to_vec(),
        }
    }

    fn autofill(
        &self,
        trial: &mut Vec<Val>,
        pos: usize,
        rule_idx: usize,
        accum: &mut Vec<Val>,
        cache: &mut HashMap<(usize, usize), AutoFillResult>,
    ) -> AutoFillResult {
        assert!(pos <= trial.len() && rule_idx <= self.rule.len());
        let key = (pos, rule_idx);

        // Base case.
        if pos == trial.len() || cache.contains_key(&key) {
            #[allow(clippy::if_same_then_else)]
            if pos == trial.len() && rule_idx != self.rule.len() {
                return AutoFillResult::Conflict;
            } else if let Some(&AutoFillResult::Conflict) = cache.get(&key) {
                return AutoFillResult::Conflict;
            }

            for (a, t) in accum[0..pos].iter_mut().zip(trial) {
                *a |= *t;
            }

            if accum
                .iter()
                .all(|&t| t < FLAG_UNKNOWN || t == FLAG_UNKNOWN | FLAG_ON | FLAG_OFF)
            {
                return AutoFillResult::SearchEnded;
            }

            return AutoFillResult::SolutionFound;
        }

        // Not enough space.
        if rule_idx < self.rule.len() {
            let required_space =
                self.rule[rule_idx..].iter().sum::<usize>() + (self.rule.len() - rule_idx - 1);

            if pos + required_space > trial.len() {
                return AutoFillResult::Conflict;
            }
        }

        let mut result = AutoFillResult::Conflict;

        // Try empty.
        if trial[pos] != FLAG_ON {
            if trial[pos] >= FLAG_UNKNOWN {
                trial[pos] = FLAG_UNKNOWN | FLAG_OFF;
            }

            match self.autofill(trial, pos + 1, rule_idx, accum, cache) {
                res @ AutoFillResult::SearchEnded => return res,
                res @ AutoFillResult::SolutionFound => result = res,
                AutoFillResult::Conflict => (),
            }
        }

        // Try filled.
        if trial[pos] != FLAG_OFF
            && rule_idx < self.rule.len()
            && pos + self.rule[rule_idx] <= trial.len()
        {
            let mut ok = true;
            let mut pos = pos;

            for _ in 0..self.rule[rule_idx] {
                if trial[pos] == FLAG_OFF {
                    ok = false;
                    break;
                } else if trial[pos] >= FLAG_UNKNOWN {
                    trial[pos] = FLAG_UNKNOWN | FLAG_ON;
                }
                pos += 1;
            }

            if ok && pos < trial.len() {
                if trial[pos] == FLAG_ON {
                    ok = false;
                } else if trial[pos] >= FLAG_UNKNOWN {
                    trial[pos] = FLAG_UNKNOWN | FLAG_OFF;
                    pos += 1;
                }
            }

            if ok {
                match self.autofill(trial, pos, rule_idx + 1, accum, cache) {
                    res @ AutoFillResult::SearchEnded => return res,
                    res @ AutoFillResult::SolutionFound => result = res,
                    AutoFillResult::Conflict => (),
                }
            }
        }

        cache.insert(key, result);
        result
    }
}

impl Constraint for Nonogram {
    fn vars(&self) -> Box<dyn Iterator<Item = &'_ VarToken> + '_> {
        Box::new(self.vars.iter())
    }

    fn on_updated(&self, search: &mut PuzzleSearch) -> PsResult<()> {
        let mut trial = vec![0; self.vars.len()];
        for (pos, &var) in trial.iter_mut().zip(&self.vars) {
            *pos = match search.get_assigned(var) {
                Some(0) => FLAG_OFF,
                Some(1) => FLAG_ON,
                _ => FLAG_UNKNOWN,
            };
        }

        let mut accum = trial.clone();
        let mut cache = HashMap::new();
        match self.autofill(&mut trial, 0, 0, &mut accum, &mut cache) {
            AutoFillResult::Conflict => return Err(Error::Default),
            AutoFillResult::SearchEnded => (),
            AutoFillResult::SolutionFound => {
                for (idx, var) in self.vars.iter().copied().enumerate() {
                    if accum[idx] == FLAG_UNKNOWN | FLAG_OFF {
                        search.set_candidate(var, 0)?;
                    } else if accum[idx] == FLAG_UNKNOWN | FLAG_ON {
                        search.set_candidate(var, 1)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn substitute(&self, _search: VarToken, _replace: VarToken) -> PsResult<Rc<dyn Constraint>> {
        unimplemented!();
    }

    fn propagate(&self, _search: &mut PuzzleSearch, _var: VarToken, _val: Val) -> PsResult<()> {
        Ok(())
    }
}

/*--------------------------------------------------------------*/

fn make_nonogram(rows: &[Vec<usize>], cols: &[Vec<usize>]) -> (Puzzle, Vec<Vec<VarToken>>) {
    let mut sys = Puzzle::new();
    let (w, h) = (cols.len(), rows.len());
    let vars = sys.new_vars_with_candidates_2d(w, h, &[0, 1]);

    for y in 0..h {
        sys.add_constraint(Nonogram::new(&vars[y], &rows[y]));
    }

    for x in 0..w {
        let tmp: Vec<_> = vars.iter().map(|row| row[x]).collect();
        sys.add_constraint(Nonogram::new(&tmp, &cols[x]));
    }

    (sys, vars)
}

fn print_nonogram(dict: &Solution, w: u32, h: u32, vars: &[Vec<VarToken>]) {
    let mut canvas = drawille::Canvas::new(w, h);

    for (y, row) in vars.iter().enumerate() {
        for (x, &var) in row.iter().enumerate() {
            if dict[var] == 1 {
                canvas.set(x as _, y as _);
            }
        }
    }

    println!("{}", canvas.frame());
}

fn verify_nonogram(dict: &Solution, vars: &[Vec<VarToken>], expected: &Board) {
    for y in 0..HEIGHT {
        for x in 0..WIDTH {
            assert_eq!(dict[vars[y][x]], expected[y][x]);
        }
    }
}

#[test]
fn nonogram_wikipedia() {
    let puzzle_rows = [
        vec![3],
        vec![5],
        vec![3, 1],
        vec![2, 1],
        vec![3, 3, 4],
        vec![2, 2, 7],
        vec![6, 1, 1],
        vec![4, 2, 2],
        vec![1, 1],
        vec![3, 1],
        vec![6],
        vec![2, 7],
        vec![6, 3, 1],
        vec![1, 2, 2, 1, 1],
        vec![4, 1, 1, 3],
        vec![4, 2, 2],
        vec![3, 3, 1],
        vec![3, 3],
        vec![3],
        vec![2, 1],
    ];

    let puzzle_cols = [
        vec![2],
        vec![1, 2],
        vec![2, 3],
        vec![2, 3],
        vec![3, 1, 1],
        vec![2, 1, 1],
        vec![1, 1, 1, 2, 2],
        vec![1, 1, 3, 1, 3],
        vec![2, 6, 4],
        vec![3, 3, 9, 1],
        vec![5, 3, 2],
        vec![3, 1, 2, 2],
        vec![2, 1, 7],
        vec![3, 3, 2],
        vec![2, 4],
        vec![2, 1, 2],
        vec![2, 2, 1],
        vec![2, 2],
        vec![1],
        vec![1],
    ];

    let expected = [
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0],
        [0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1],
        [0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ];

    let (mut sys, vars) = make_nonogram(&puzzle_rows, &puzzle_cols);
    let dict = sys.solve_unique().expect("solution");
    print_nonogram(&dict, puzzle_cols.len() as _, puzzle_rows.len() as _, &vars);
    verify_nonogram(&dict, &vars, &expected);
    println!("nonogram_wikipedia: {} guesses.", sys.num_guesses());
}
