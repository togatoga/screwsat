# screwsat

[![Crates.io](https://img.shields.io/crates/v/screwsat)](https://crates.io/crates/screwsat)

A simple CDCL(Conflict-Driven-Clause-Learning) SAT Solver in `Rust`.  
I wrote it very simple to help people(including me) understand the inside of SAT Solver.  


I have implemented the core SAT Solver algorithms and techniques in `screwsat`.  
#### Algorithms and Techniques
- CDCL(Conflict-Driven-Clause-Learning)
- Back Jump
- Two-Literal-Watching

The performance of `screwsat` isn't as good as other modern sat solvers.  
But you can grasp some important points of SAT Solver from `screwsat`(I hope).  


`screwsat` is written in only one file and `std` libraries. You can use it for competitive programming problems.  

#### Accepted by `screwsat`
- [AtCoder Beginner Contest 187 F - Close Group](https://atcoder.jp/contests/abc187/submissions/19235301)
- [天下一プログラマーコンテスト2016本戦（オープンコンテスト） B - 今年の B 問題](https://atcoder.jp/contests/tenka1-2016-final-open/submissions/19375260)


#### Testing

You need to pull all SAT problems under the `cnf` directory that are stored by [`git-lfs`](https://git-lfs.github.com/) to run `cargo test`.

```
% git lfs pull
% cargo test -- --nocapture
```

## How to use

`screwsat` can be used as a library and a command-line tool.

## Command

### Install

```bash
% cargo install --locked screwsat
```

### Usage(cmd)

```bash
% screwsat --help
USAGE: screwsat [options] <input-file> [output-file]

% cat examples/sat.cnf
c Here is a comment.
c SATISFIABLE
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0

% screwsat examples/sat.cnf
s SATISFIABLE
-1 -2 -3 -4 -5 0

% screwsat cnf/unsat/unsat.cnf
s UNSATISFIABLE

% screwsat examples/sat.cnf sat_result.txt
% cat sat_result.txt
SAT
-1 -2 -3 -4 -5 0

```

## Library

You need to add `screwsat` to `Cargo.toml`.

```toml
screwsat="*"
```

OR

Copy `src/lib.rs` and Paste it. (Competitive Programming Style)

### Usage(lib)

```rust
use std::vec;

use screwsat::solver::*;
use screwsat::util;
fn main() {
    {
        // Create a default Solver struct
        let mut solver = Solver::default();
        // A problem is (x1 v ¬x5 v x4) ∧ (¬x1 v x5 v x3 v x4) ∧ (x3 v x4)
        let clauses = vec![
            // (x1 v ¬x5 v x4)
            vec![Lit::from(1), Lit::from(-5), Lit::from(4)],
            // (¬x1 v x5 v x3 v x4)
            vec![Lit::from(-1), Lit::from(5), Lit::from(3), Lit::from(4)],
            // (x3 v x4)
            vec![Lit::from(3), Lit::from(4)],
        ];
        // Add clauses to solver
        clauses
            .into_iter()
            .for_each(|clause| solver.add_clause(&clause));

        let status = solver.solve(None);
        // Sat: A problem is SATISFIABLE.
        println!("{:?}", status);
        // print the assignments satisfy a given problem.
        // x1 = false x2 = false x3 = false x4 = true x5 = false
        solver
            .assigns
            .iter()
            .enumerate()
            .for_each(|(var, assign)| print!("x{} = {} ", var + 1, assign));
        println!("");
    }

    {
        // Parse a DIMACS CNF file
        // c
        // c This is a sample input file.
        // c (unsatisfiable)
        // c
        // p cnf 3 5
        // 1 -2 3 0
        // -1 2 0
        // -2 -3 0
        // 1 2 -3 0
        // 1 3 0
        // -1 -2 3 0
        let cnf = util::parse_cnf("examples/unsat.cnf").unwrap();
        // 3
        let variable_num = cnf.var_num.unwrap();
        // 5
        //let clause_num = cnf.cla_num.unwrap();

        let clauses = cnf.clauses;
        // Create a new Solver struct
        let mut solver = Solver::new(variable_num, &clauses);
        let status = solver.solve(None);
        // Unsat: A problem is UNSATISFIABLE
        println!("{:?}", status);
    }

    {
        // Set the time limitation
        // You might want to set the time limitation for very hard problem
        let cnf = util::parse_cnf("examples/hard.cnf").unwrap();
        let mut solver = Solver::default();
        let clauses = cnf.clauses;
        clauses
            .into_iter()
            .for_each(|clause| solver.add_clause(&clause));
        // 5 sec
        let status = solver.solve(Some(std::time::Duration::from_secs(5)));
        // Indeterminate
        println!("{:?}", status);
    }
}

```

### Appreciation

This code is really inspired by his good simple code [not522's SAT Solver](https://github.com/not522/CompetitiveProgramming/blob/master/include/math/sat.hpp)

### Contribution
Contributions and feedbacks are welcome. (e.g., fix typo and tedious code and my English, report bugs/issues, **GIVE ME GITHUB STARS**)