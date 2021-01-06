# screwsat

[![Crates.io](https://img.shields.io/crates/v/screwsat)](https://crates.io/crates/screwsat)

A very simple CDCL(Conflict-Driven-Clause-Learning) SAT Solver in `Rust`. The line of `solver` is around `300` lines.  
I wrote it very simple to help people(including me) understating the inside of SAT Solver.  
The performance of `screwsat` isn't good enough. You can easily understand the inside of SAT Solver(I hope).

## How to use

`screwsat` can be used as a library and a command line tool. 

## Command

### Install

```bash
% cargo install --locked screwsat
```

### Usage

```bash
% screwsat --help
USAGE: screwsat [options] <input-file> [output-file]

% cat cnf/sat/sat.cnf
c Here is a comment.
c SATISFIABLE
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0

% screwsat cnf/sat/sat.cnf
s SATISFIABLE
-1 -2 -3 -4 -5 0

% screwsat cnf/unsat/unsat.cnf
s UNSATISFIABLE

% screwsat cnf/sat/sat.cnf sat_result.txt
% cat sat_result.txt
SAT
-1 -2 -3 -4 -5 0

```

## Library

You can add `screwsat` to `Cargo.toml`.

```toml
screwsat="1.0"
```

OR

Copy `src/lib.rs` and Paste it.(Competitive Programming Style)

### Usage

```rust
use std::vec;

use screwsat::solver::Solver;
use screwsat::util;
fn main() {
    {
        // Create a default Solver struct
        let mut solver = Solver::default();
        // A problem is (x1 v ¬x5 v x4) ^ (¬x1 v x5 v x3 v x4)　^ (¬x3 v x4)
        let clauses = vec![
            // (x1 v ¬x5 v x4)
            vec![(0, true), (4, false), (3, true)],
            // (¬x1 v x5 v x3 v x4)
            vec![(0, false), (4, true), (2, true), (3, true)],
            // (¬x3 v x4)
            vec![(2, false), (3, false)],
        ];
        // Add clauses to solver
        clauses
            .into_iter()
            .for_each(|clause| solver.add_clause(&clause));

        let status = solver.solve(None);
        // Sat: A problem is SATISFIABLE.
        println!("{:?}", status);
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
        let cnf = util::parse_cnf("cnf/unsat/unsat.cnf").unwrap();
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
        clauses.into_iter().for_each(|clause| solver.add_clause(&clause));
        // 5 sec
        let status = solver.solve(Some(std::time::Duration::from_secs(5)));
        // Indeterminate
        println!("{:?}", status);
    }
}
```

### Appreciation

This code is really inspired by his simple good code [not522's SAT Solver](https://github.com/not522/CompetitiveProgramming/blob/master/include/math/sat.hpp).
### Other

Make a merge request and give me start makes me motivated.