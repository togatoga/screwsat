use screwsat::{solver, util};
use solver::LitBool;

use std::{env, fs::File};
fn help(msg: Option<&str>) {
    if let Some(msg) = msg {
        println!("{}", msg);
    }
    println!("USAGE: screwsat [options] <input-file> [output-file]");
}

fn print_result<W: std::io::Write>(
    solver: solver::Solver,
    status: solver::Status,
    mut writer: W,
    to_file: bool,
) -> std::io::Result<()> {
    match status {
        solver::Status::Sat => {
            if to_file {
                writeln!(writer, "SAT")?;
            } else {
                writeln!(writer, "s SATISFIABLE")?;
            }
            for (v, &b) in solver.assigns.iter().enumerate() {
                let res = if b == LitBool::True {
                    (v + 1) as i32
                } else {
                    -((v + 1) as i32)
                };
                write!(writer, "{} ", res)?;
            }
            writeln!(writer, "0")?;
        }
        solver::Status::Unsat => {
            if to_file {
                writeln!(writer, "UNSAT")?;
            } else {
                writeln!(writer, "s UNSATISFIABLE")?;
            }
        }
        solver::Status::Indeterminate => {
            writeln!(writer, "s INDETERMINATE")?;
        }
    };
    writer.flush()?;
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() == 1 {
        help(Some("No input file"));
        std::process::exit(1);
    }
    let mut rest_args = vec![];
    args.iter().skip(1).for_each(|arg| {
        if arg.starts_with('-') {
            if arg == "-h" || arg == "--help" {
                help(None);
                std::process::exit(0);
            }
        } else {
            rest_args.push(arg.clone());
        }
    });
    if rest_args.is_empty() {
        help(Some("No input file"));
        std::process::exit(1);
    }

    if rest_args.len() > 2 {
        help(Some("Too many arguments"));
        std::process::exit(1);
    }
    let input_file = &rest_args[0];
    let output_file = rest_args.get(1);
    let input = std::fs::File::open(input_file).unwrap();
    let mut solver = match util::parse_cnf(input) {
        Ok(result) => {
            let mut solver = solver::Solver::default();

            if let Some(var_num) = result.var_num {
                solver.reserve_variable(var_num);
                while var_num > solver.assigns.len() {
                    solver.new_var();
                }
            }
            if let Some(cla_num) = result.cla_num {
                solver.reserve_clause(cla_num);
            }
            result.clauses.iter().for_each(|clause| {
                solver.add_clause(clause);
            });
            solver
        }
        Err(e) => {
            println!("{}", e);
            std::process::exit(1);
        }
    };

    let status = solver.solve(None);
    let (writer, to_file): (Box<dyn std::io::Write>, bool) = if let Some(output_file) = output_file
    {
        let f =
            File::create(output_file).unwrap_or_else(|_| panic!("Failed to open {}", output_file));
        (Box::new(f), true)
    } else {
        (Box::new(std::io::stdout()), false)
    };
    if let Err(e) = print_result(solver, status, writer, to_file) {
        println!("{}", e);
        std::process::exit(1);
    }
    std::process::exit(0);
}
