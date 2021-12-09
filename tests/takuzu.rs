//! Takuzu (A.K.A. Binairo).
//!
//! https://en.wikipedia.org/wiki/Takuzu

extern crate puzzle_solver;

use puzzle_solver::*;
use std::iter;
use std::rc::Rc;

const X: Val = -1;

/*--------------------------------------------------------------*/
#[derive(Debug)]
struct BinaryRepr {
    // value = sum_i 2^i bits[i]
    value: VarToken,
    bits: Vec<VarToken>,
}

impl Constraint for BinaryRepr {
    fn vars<'a>(&'a self) -> Box<dyn Iterator<Item = &'a VarToken> + 'a> {
        Box::new(iter::once(&self.value).chain(&self.bits))
    }

    fn on_assigned(&self, search: &mut PuzzleSearch, var: VarToken, val: Val) -> PsResult<()> {
        if var == self.value {
            let mut val = val;
            for &var in self.bits.iter() {
                search.set_candidate(var, val & 1)?;
                val >>= 1;
            }
        } else if let Some(bitpos) = self.bits.iter().position(|&v| v == var) {
            let bit = 1 << bitpos;
            let discard = search
                .get_unassigned(self.value)
                .filter(|c| c & bit != val * bit)
                .collect::<Vec<_>>();

            for c in discard.into_iter() {
                search.remove_candidate(self.value, c)?;
            }
        }

        Ok(())
    }

    fn substitute(&self, _from: VarToken, _to: VarToken) -> PsResult<Rc<dyn Constraint>> {
        unimplemented!();
    }
}

/*--------------------------------------------------------------*/

fn make_sums(size: usize) -> Vec<Val> {
    let mut vec = Vec::new();

    for val in 0..(1 << size) {
        let mut count = 0;
        let mut v = val as usize;

        while v > 0 {
            count += v & 1;
            v >>= 1;
        }

        if count == size / 2 {
            vec.push(val);
        }
    }

    vec
}

fn make_takuzu(puzzle: &[Vec<Val>]) -> (Puzzle, Vec<Vec<VarToken>>) {
    let height = puzzle.len();
    assert!(height > 0 && height % 2 == 0);
    let width = puzzle[0].len();
    assert!(width > 0 && width % 2 == 0);

    let row_candidates = make_sums(height);
    let col_candidates = make_sums(width);

    let mut sys = Puzzle::new();
    let vars = sys.new_vars_with_candidates_2d(width, height, &[0, 1]);
    let row_values = sys.new_vars_with_candidates_1d(height, &row_candidates);
    let col_values = sys.new_vars_with_candidates_1d(width, &col_candidates);

    for y in 0..height {
        let total = (height as Val) / 2;
        sys.equals(
            total,
            vars[y].iter().fold(LinExpr::from(0), |sum, &x| sum + x),
        );
        sys.add_constraint(BinaryRepr {
            value: row_values[y],
            bits: vars[y].clone(),
        });
    }

    for x in 0..width {
        let total = (width as Val) / 2;
        sys.equals(
            total,
            vars.iter().fold(LinExpr::from(0), |sum, row| sum + row[x]),
        );
        sys.add_constraint(BinaryRepr {
            value: col_values[x],
            bits: (0..height).map(|y| vars[y][x]).collect(),
        });
    }

    // No three in a row, i.e. not: 000, 111.
    for y in 0..height {
        for window in vars[y].windows(3) {
            let disjunction = sys.new_var_with_candidates(&[1, 2]);
            sys.equals(window[0] + window[1] + window[2], disjunction);
        }
    }

    for x in 0..width {
        for y in 0..(height - 2) {
            let disjunction = sys.new_var_with_candidates(&[1, 2]);
            sys.equals(
                vars[y + 0][x] + vars[y + 1][x] + vars[y + 2][x],
                disjunction,
            );
        }
    }

    sys.all_different(&row_values);
    sys.all_different(&col_values);

    for y in 0..height {
        for x in 0..width {
            if puzzle[y][x] != X {
                sys.set_value(vars[y][x], puzzle[y][x]);
            }
        }
    }

    (sys, vars)
}

fn print_takuzu(dict: &Solution, vars: &[Vec<VarToken>]) {
    for row in vars.iter() {
        let sum = row.iter().fold(0, |sum, &var| 2 * sum + dict[var]);
        for &var in row.iter() {
            print!("{}", dict[var]);
        }
        println!(" = {}", sum);
    }
}

fn verify_takuzu(dict: &Solution, vars: &[Vec<VarToken>], expected: &[Val]) {
    for (row, &expected) in vars.iter().zip(expected) {
        let sum = row.iter().fold(0, |sum, &var| 2 * sum + dict[var]);
        assert_eq!(sum, expected);
    }
}

#[test]
fn takuzu_grid1() {
    let puzzle = vec![
        vec![X, 1, 0, X, X, X],
        vec![1, X, X, X, 0, X],
        vec![X, X, 0, X, X, X],
        vec![1, 1, X, X, 1, 0],
        vec![X, X, X, X, 0, X],
        vec![X, X, X, X, X, X],
    ];

    let (mut sys, vars) = make_takuzu(&puzzle);
    let solutions = sys.solve_all();
    assert_eq!(solutions.len(), 6);

    print_takuzu(&solutions[0], &vars);
    println!("takuzu_grid1: {} guesses", sys.num_guesses());
}

#[test]
fn takuzu_grid2() {
    let puzzle = vec![
        vec![0, X, X, X, X, 1, 1, X, X, 0, X, X],
        vec![X, X, X, 1, X, X, X, 0, X, X, X, X],
        vec![X, 0, X, X, X, X, 1, X, X, X, 0, 0],
        vec![1, X, X, 1, X, X, 1, 1, X, X, X, 1],
        vec![X, X, X, X, X, X, X, X, X, 1, X, X],
        vec![0, X, 0, X, X, X, 1, X, X, X, X, X],
        vec![X, X, X, X, 0, X, X, X, X, X, X, X],
        vec![X, X, X, X, 0, 1, X, 0, X, X, X, X],
        vec![X, X, 0, 0, X, X, 0, X, 0, X, X, 0],
        vec![X, X, X, X, X, 1, X, X, X, X, 1, X],
        vec![1, 0, X, 0, X, X, X, X, X, X, X, X],
        vec![X, X, 1, X, X, X, X, 1, X, X, 0, 0],
    ];

    let expected = [
        0b_0101_0110_1001,
        0b_0101_0100_1011,
        0b_1010_1011_0100,
        0b_1001_0011_0011,
        0b_0110_1100_1100,
        0b_0100_1011_0011,
        0b_1011_0010_1010,
        0b_0011_0100_1101,
        0b_1100_1001_0110,
        0b_0101_0110_1010,
        0b_1010_1001_0101,
        0b_1010_1101_0100,
    ];

    let (mut sys, vars) = make_takuzu(&puzzle);
    let dict = sys.solve_unique().expect("solution");
    print_takuzu(&dict, &vars);
    verify_takuzu(&dict, &vars, &expected);
    println!("takuzu_grid2: {} guesses", sys.num_guesses());
}

#[test]
fn takuzu_grid3() {
    let puzzle = vec![
        vec![X, X, X, 0, X, 0, X, X, X, X, 0, X],
        vec![1, X, X, X, X, X, X, 1, X, X, X, 1],
        vec![X, X, 1, 1, X, X, X, X, X, X, 0, X],
        vec![X, 0, X, X, X, X, X, X, X, X, X, 0],
        vec![X, X, X, 0, X, X, 1, 1, 0, X, X, X],
        vec![0, X, 0, 0, X, 0, X, 1, X, X, 0, X],
        vec![X, X, X, X, X, X, 0, X, X, X, 0, X],
        vec![1, X, 1, X, 0, X, X, X, X, X, X, X],
        vec![X, X, X, X, X, X, 1, 0, 1, X, 0, X],
        vec![X, 1, X, X, 0, X, X, X, X, 0, 0, X],
        vec![X, X, X, 1, X, X, X, 0, X, X, X, X],
        vec![X, X, X, X, X, 1, 1, X, X, 1, X, X],
    ];

    let expected = [
        0b_1010_1001_1001,
        0b_1100_1001_0011,
        0b_0011_0110_1100,
        0b_1011_0100_1010,
        0b_0100_1011_0011,
        0b_0100_1011_0101,
        0b_1011_0100_1100,
        0b_1011_0101_0010,
        0b_0100_1010_1101,
        0b_0110_0101_1001,
        0b_1001_1010_0110,
        0b_0101_0110_0110,
    ];

    let (mut sys, vars) = make_takuzu(&puzzle);
    let dict = sys.solve_unique().expect("solution");
    print_takuzu(&dict, &vars);
    verify_takuzu(&dict, &vars, &expected);
    println!("takuzu_grid3: {} guesses", sys.num_guesses());
}

#[test]
fn takuzu_grid4() {
    let puzzle = vec![
        vec![X, X, X, X, X, 1, 1, X, X, 0, X, X],
        vec![X, X, X, 1, X, X, X, 0, X, X, X, X],
        vec![X, 0, X, X, X, X, 1, X, X, X, 0, 0],
        vec![X, X, X, 1, X, X, 1, 1, X, X, X, 1],
        vec![X, X, X, X, X, X, X, X, X, 1, X, X],
        vec![X, X, 0, X, X, X, 1, X, X, X, X, X],
        vec![X, X, X, X, 0, X, X, X, X, X, X, X],
        vec![X, X, X, X, 0, 1, X, 0, X, X, X, X],
        vec![X, X, 0, 0, X, X, 0, X, 0, X, X, 0],
        vec![X, X, X, X, X, 1, X, X, X, X, 1, X],
        vec![X, X, X, 0, X, X, X, X, X, X, X, X],
        vec![X, X, 1, X, X, X, X, 1, X, X, 0, 0],
    ];

    let (mut sys, vars) = make_takuzu(&puzzle);
    let dict = sys.solve_any().expect("solution");
    print_takuzu(&dict, &vars);
    println!("takuzu_grid4: {} guesses", sys.num_guesses());
}
