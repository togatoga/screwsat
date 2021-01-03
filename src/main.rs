use screwsat::screwsat;
use std::io::BufRead;
use std::{env, fs::File};
fn help(msg: Option<&str>) {
    if let Some(msg) = msg {
        println!("{}", msg);
    }
    println!("USAGE: screwsat [options] <input-file> [output-file]");
}

struct ParsedResult {
    var_num: Option<usize>,
    cla_num: Option<usize>,
    clauses: Vec<Vec<screwsat::Lit>>,
}
// c Here is a comment.
// c SATISFIABLE
// p cnf 5 3
// 1 -5 4 0
// -1 5 3 4 0
// -3 -4 0
fn parse_cnf(input_file: &str) -> std::io::Result<ParsedResult> {
    let file = std::fs::File::open(input_file)?;
    let reader = std::io::BufReader::new(file);
    let mut var_num = None;
    let mut cla_num = None;
    let mut clauses = vec![];
    for (num, line) in reader.lines().enumerate() {
        let line = line?;
        if line.starts_with('c') {
            //comment
            continue;
        }
        let values: Vec<&str> = line.split_whitespace().collect();
        if values.is_empty() {
            continue;
        }
        if values[0] == "p" {
            //p cnf v_num c_num
            if let Some(v) = values.get(2) {
                var_num = Some(v.parse::<usize>().unwrap());
            };
            if let Some(v) = values.get(3) {
                cla_num = Some(v.parse::<usize>().unwrap());
            }
            continue;
        }

        let values: Vec<_> = values
            .iter()
            .map(|x| x.parse::<i32>().unwrap())
            .take_while(|x| *x != 0)
            .collect();

        if values.is_empty() {
            println!("Invalid Line {} : {}", num, line);
            std::process::exit(1);
        }
        let clause: Vec<screwsat::Lit> = values
            .iter()
            .map(|&x| {
                let d = x.abs() as screwsat::Var;
                if x > 0 {
                    (d - 1, true)
                } else {
                    (d - 1, false)
                }
            })
            .collect();
        clauses.push(clause);
    }
    Ok(ParsedResult {
        var_num,
        cla_num,
        clauses,
    })
}

fn print_result<W: std::io::Write>(
    solver: screwsat::Solver,
    status: screwsat::Status,
    mut writer: W,
    to_file: bool,
) -> std::io::Result<()> {
    match status {
        screwsat::Status::Sat => {
            if to_file {
                writeln!(writer, "SAT")?;
            } else {
                writeln!(writer, "s SATISFIABLE")?;
            }
            for (v, &b) in solver.assigns.iter().enumerate() {
                let res = if b { (v + 1) as i32 } else { -((v + 1) as i32) };
                write!(writer, "{} ", res)?;
            }
            writeln!(writer, "0")?;
        }
        screwsat::Status::Unsat => {
            if to_file {
                writeln!(writer, "UNSAT")?;
            } else {
                writeln!(writer, "s UNSATISFIABLE")?;
            }
        }
        screwsat::Status::Indeterminate => {
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
    let mut solver = match parse_cnf(&input_file) {
        Ok(result) => {
            let mut solver = screwsat::Solver::default();

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
