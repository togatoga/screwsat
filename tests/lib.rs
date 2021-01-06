#[cfg(test)]
mod tests {
    use screwsat::solver::{Solver, Status};
    use screwsat::util;
    use std::fs::{self};

    fn test_all_files(which: &str) {
        let expected = if which == "sat" {
            Status::Sat
        } else {
            Status::Unsat
        };
        let entries = fs::read_dir(format!("cnf/{}/", which)).unwrap();
        entries.for_each(|entry| {
            let p = entry.unwrap().path();
            let path_str = p.to_str().unwrap();
            if path_str.ends_with(".cnf") {
                //parse cnf file
                let cnf = util::parse_cnf(path_str).unwrap();
                let mut solver = Solver::default();
                cnf.clauses
                    .iter()
                    .for_each(|clause| solver.add_clause(clause));
                let status = solver.solve(None);
                if status != expected {
                    eprintln!(
                        "cnf: {}, Result: {:?} Expected: {:?}",
                        path_str, status, expected
                    );
                    assert!(false);
                }
            }
        });
    }
    #[test]
    fn test_solve() {
        test_all_files("sat");
        test_all_files("unsat");
    }
}
