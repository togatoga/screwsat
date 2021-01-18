#[cfg(test)]
mod tests {
    use screwsat::solver::*;

    use screwsat::util;

    use walkdir::WalkDir;
    fn sat_model_check(clauses: &[Vec<Lit>], assigns: &[bool]) -> bool {
        for clause in clauses.iter() {
            let mut satisfied = false;
            for lit in clause {
                if assigns[lit.var().0 as usize] == lit.pos() {
                    satisfied = true;
                    break;
                }
            }
            if !satisfied {
                return false;
            }
        }
        true
    }

    #[allow(dead_code)]
    fn clauses_to_cnf(clauses: &[Vec<Lit>], output_file_name: &str) -> std::io::Result<()> {
        use std::io::prelude::*;

        let mut f = std::fs::File::create(output_file_name)?;
        let mut var_num = 0;
        clauses.iter().for_each(|clause| {
            for c in clause.iter() {
                var_num = std::cmp::max(var_num, c.var().0 + 1);
            }
        });
        writeln!(f, "p cnf {} {}", var_num, clauses.len())?;
        for clause in clauses.iter() {
            let line = clause
                .iter()
                .enumerate()
                .map(|(i, x)| {
                    let v = if x.pos() {
                        format!("{}", x.var().0 + 1)
                    } else {
                        format!("-{}", x.var().0 + 1)
                    };
                    if i == clause.len() - 1 {
                        format!("{} 0", v)
                    } else {
                        format!("{} ", v)
                    }
                })
                .collect::<String>();
            writeln!(f, "{}", line)?;
        }
        Ok(())
    }
    fn test_all_files(which: &str) {
        let expected = if which == "sat" {
            Status::Sat
        } else {
            Status::Unsat
        };
        let entries = WalkDir::new(format!("cnf/{}/", which));
        for entry in entries
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| !e.file_type().is_dir())
        {
            let path_str = entry.path().to_str().unwrap();

            if path_str.ends_with(".cnf") {
                //parse cnf file
                let input = std::fs::File::open(path_str).unwrap();
                let cnf = util::parse_cnf(input).unwrap();
                let mut solver = Solver::default();
                cnf.clauses
                    .iter()
                    .for_each(|clause| solver.add_clause(clause));

                eprintln!("Solving... {}", path_str);
                // Time limit is 10 sec
                let status = solver.solve(Some(std::time::Duration::from_secs(10)));
                assert!(solver.status == Some(status));
                //Time out
                if status == Status::Indeterminate {
                    eprintln!("Skip!!(TIME LIMIT EXCEEDED): {}", path_str);
                    continue;
                }
                if status != expected {
                    eprintln!(
                        "cnf: {}, Result: {:?} Expected: {:?}",
                        path_str, status, expected
                    );
                    assert!(false);
                }
                if status == Status::Sat {
                    if !sat_model_check(&cnf.clauses, &solver.assigns) {
                        eprintln!(
                            "Assignments are wrong!! cnf: {}, Result: {:?} Expected: {:?}",
                            path_str, status, expected
                        );
                        assert!(false);
                    }
                }
            }
        }
    }
    #[test]
    fn test_solve() {
        test_all_files("sat");
        test_all_files("unsat");
    }
}
