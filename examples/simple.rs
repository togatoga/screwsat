use std::vec;

use screwsat::solver::Solver;
use screwsat::util;
fn main() {
    {
        // Create a default Solver struct
        let mut solver = Solver::default();
        // A problem is (x1 v ¬x5 v x4) ∧ (¬x1 v x5 v x3 v x4) ∧ (x3 v x4)
        let clauses = vec![
            // (x1 v ¬x5 v x4)
            vec![(0, true), (4, false), (3, true)],
            // (¬x1 v x5 v x3 v x4)
            vec![(0, false), (4, true), (2, true), (3, true)],
            // (x3 v x4)
            vec![(2, true), (3, true)],
        ];
        // Add clauses to solver
        clauses
            .into_iter()
            .for_each(|clause| solver.add_clause(clause));

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
