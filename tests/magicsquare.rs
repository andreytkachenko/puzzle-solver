//! Magic Square.
//!
//! https://en.wikipedia.org/wiki/Magic_square

use puzzle_solver::{LinExpr, Puzzle, Solution, Val, VarToken};

fn make_magic_square(n: usize) -> (Puzzle, Vec<Vec<VarToken>>, VarToken) {
    let mut sys = Puzzle::new();
    let digits = 1..(n * n + 1) as Val;
    let vars = sys.new_vars_2d(n, n, digits.clone());

    // Calculate the range of the total (in a dumb way).
    let min = digits.clone().into_iter().take(n).sum();
    let max = digits.clone().into_iter().rev().take(n).sum();
    let total = sys.new_var(min..max);

    sys.all_different(vars.iter().flatten());

    for y in 0..n {
        sys.equals(
            total,
            vars[y].iter().fold(LinExpr::from(0), |sum, &x| sum + x),
        );
    }

    for x in 0..n {
        sys.equals(
            total,
            vars.iter().fold(LinExpr::from(0), |sum, row| sum + row[x]),
        );
    }

    {
        sys.equals(
            total,
            (0..n).fold(LinExpr::from(0), |sum, i| sum + vars[i][i]),
        );
        sys.equals(
            total,
            (0..n).fold(LinExpr::from(0), |sum, i| sum + vars[i][n - i - 1]),
        );
    }

    // Sum of all digits = sum of all rows (columns) = total * n.
    sys.equals(total * (n as Val), digits.into_iter().sum::<Val>());

    (sys, vars, total)
}

fn print_magic_square(dict: &Solution, vars: &[Vec<VarToken>]) {
    for row in vars.iter() {
        for &var in row.iter() {
            print!(" {:2}", dict[var]);
        }
        println!();
    }
}

#[test]
fn magicsquare_3x3() {
    let (mut sys, vars, total) = make_magic_square(3);
    let solutions = sys.solve_all();
    assert_eq!(solutions.len(), 8);

    print_magic_square(&solutions[0], &vars);
    for dict in solutions.iter() {
        assert_eq!(dict[total], 15);
    }
    println!("magicsquare_3x3: {} guesses", sys.num_guesses());
}

#[test]
fn magicsquare_4x4() {
    let (mut sys, vars, total) = make_magic_square(4);
    let dict = sys.solve_any().expect("solution");
    print_magic_square(&dict, &vars);
    assert_eq!(dict[total], 34);
}
