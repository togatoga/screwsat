use screwsat::solver::*;
use screwsat::util;
use std::collections::HashMap;

fn lit_from_pos_and_val(n: usize, y: usize, x: usize, val: usize) -> Lit {
    // x_y_x_v
    (n * n * y + n * x + (val - 1), true)
}
/// n by n Sudoku
/// Sudoku Condition:
/// `x_r_w_v = true` means that the cell (r, w) is assigned to `v`(1~n)
/// Conditions
/// 1. one cell is either one of 1 to n.(at least)
/// 2. one cell can't be assigned to multiple values.(at most)
/// 3. cells that are in same row/col/block can't be assigned to same value.(at most)
/// 4. cells are filled by a board value
fn clauses_from_sudoku(board: &[Vec<u32>]) -> Vec<Vec<Lit>> {
    let n: usize = board.len();

    let mut cell_to_lits = HashMap::new();
    for r in 0..n {
        for c in 0..n {
            // x_r_c_v
            let clause: Vec<Lit> = (1..=n)
                .map(|val| lit_from_pos_and_val(n, r, c, val))
                .collect();
            cell_to_lits.insert((r, c), clause);
        }
    }

    let mut clauses = vec![];
    for r in 0..n {
        for c in 0..n {
            let clause = cell_to_lits.get(&(r, c)).unwrap();
            // 1.
            clauses.push(clause.clone());
            // 2.
            for (i, &l1) in clause.iter().enumerate() {
                for &l2 in clause.iter().skip(i + 1) {
                    clauses.push(vec![l1.neg(), l2.neg()]);
                }
            }
        }
    }
    // 3. row
    for c in 0..n {
        for r1 in 0..n {
            for r2 in r1 + 1..n {
                let clause1 = cell_to_lits.get(&(r1, c)).unwrap();
                let clause2 = cell_to_lits.get(&(r2, c)).unwrap();
                for v in 1..=n {
                    clauses.push(vec![clause1[v - 1].neg(), clause2[v - 1].neg()]);
                }
            }
        }
    }
    // 3. col
    for r in 0..n {
        for c1 in 0..n {
            for c2 in c1 + 1..n {
                let clause1 = cell_to_lits.get(&(r, c1)).unwrap();
                let clause2 = cell_to_lits.get(&(r, c2)).unwrap();
                for v in 1..=n {
                    clauses.push(vec![clause1[v - 1].neg(), clause2[v - 1].neg()]);
                }
            }
        }
    }

    // 3. block
    let block = (n as f64).sqrt() as usize;
    for r_b in 0..block {
        for c_b in 0..block {
            let rs = r_b * block;
            let cs = c_b * block;

            let mut block_indices = vec![];
            for r1 in 0..block {
                for c1 in 0..block {
                    block_indices.push((rs + r1, cs + c1));
                }
            }

            for (i, p1) in block_indices.iter().enumerate() {
                for p2 in block_indices.iter().skip(i + 1) {
                    let (r1, c1) = *p1;
                    let (r2, c2) = *p2;
                    let clause1 = cell_to_lits.get(&(r1, c1)).unwrap();
                    let clause2 = cell_to_lits.get(&(r2, c2)).unwrap();
                    for v in 1..=9 {
                        clauses.push(vec![clause1[v - 1].neg(), clause2[v - 1].neg()]);
                    }
                }
            }
        }
    }

    for y in 0..n {
        for x in 0..n {
            if board[y][x] > 0 {
                let lit = lit_from_pos_and_val(n, y, x, board[y][x] as usize);
                clauses.push(vec![lit]);
            }
        }
    }
    clauses
}

fn print_sudoku(board: &[Vec<u32>], colored: &[Vec<u32>]) {
    let n = board.len();
    let mut results = vec![];
    println!("Sudoku {} x {}", n, n);
    for y in 0..n {
        let line: String = board[y]
            .iter()
            .enumerate()
            .map(|(x, v)| {
                if colored[y][x] > 0 {
                    //color red
                    format!("\x1b[{}m{:02}\x1b[m ", 31, v)
                } else {
                    format!("{:02} ", v)
                }
            })
            .collect();
        results.push(line);
    }
    // print results
    let line: String = (0..2 * n + 10).map(|_| "-").collect();
    println!("{}", line);
    results.iter().for_each(|line| {
        println!("{}", line);
    });
    println!("{}", line);
    println!();
}

fn board_from_assign(n: usize, assigns: &[bool]) -> Vec<Vec<u32>> {
    let mut board = vec![vec![0; n]; n];
    for y in 0..n {
        for x in 0..n {
            for v in 1..=n {
                let var = lit_from_pos_and_val(n, y, x, v).0;
                if assigns[var] {
                    board[y][x] = v as u32;
                    break;
                }
            }
        }
    }
    board
}

fn main() {
    {
        let mut solver = Solver::default();
        let sudoku_9 = [
            vec![0, 0, 5, 3, 0, 0, 0, 0, 0],
            vec![8, 0, 0, 0, 0, 0, 0, 2, 0],
            vec![0, 7, 0, 0, 1, 0, 5, 0, 0],
            vec![4, 0, 0, 0, 0, 5, 3, 0, 0],
            vec![0, 1, 0, 0, 7, 0, 0, 0, 6],
            vec![0, 0, 3, 2, 0, 0, 0, 8, 0],
            vec![0, 6, 0, 5, 0, 0, 0, 0, 9],
            vec![0, 0, 4, 0, 0, 0, 0, 3, 0],
            vec![0, 0, 0, 0, 0, 9, 7, 0, 0],
        ];
        print_sudoku(&sudoku_9, &sudoku_9);
        let clauses = clauses_from_sudoku(&sudoku_9);
        clauses.iter().for_each(|clause| solver.add_clause(clause));
        let status = solver.solve(None);
        match status {
            Status::Sat => {
                println!("SAT");
                let result = board_from_assign(sudoku_9.len(), &solver.assigns);
                if !util::sat_model_check(&clauses, &solver.assigns) {
                    panic!("Assignments are wrong!!");
                }
                print_sudoku(&result, &sudoku_9);
            }
            Status::Unsat => {
                println!("UNSAT");
            }
            _ => {
                println!("INDETERMINATE");
            }
        }
    }

    {
        let mut solver = Solver::default();
        let sudoku_16 = [
            vec![0, 15, 0, 1, 0, 2, 10, 14, 12, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 6, 3, 16, 12, 0, 8, 4, 14, 15, 1, 0, 2, 0, 0, 0],
            vec![14, 0, 9, 7, 11, 3, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![4, 13, 2, 12, 0, 0, 0, 0, 6, 0, 0, 0, 0, 15, 0, 0],
            vec![0, 0, 0, 0, 14, 1, 11, 7, 3, 5, 10, 0, 0, 8, 0, 12],
            vec![3, 16, 0, 0, 2, 4, 0, 0, 0, 14, 7, 13, 0, 0, 5, 15],
            vec![11, 0, 5, 0, 0, 0, 0, 0, 0, 9, 4, 0, 0, 6, 0, 0],
            vec![0, 0, 0, 0, 13, 0, 16, 5, 15, 0, 0, 12, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 9, 0, 1, 12, 0, 8, 3, 10, 11, 0, 15, 0],
            vec![2, 12, 0, 11, 0, 0, 14, 3, 5, 4, 0, 0, 0, 0, 9, 0],
            vec![6, 3, 0, 4, 0, 0, 13, 0, 0, 11, 9, 1, 0, 12, 16, 2],
            vec![0, 0, 10, 9, 0, 0, 0, 0, 0, 0, 12, 0, 8, 0, 6, 7],
            vec![12, 8, 0, 0, 16, 0, 0, 10, 0, 13, 0, 0, 0, 5, 0, 0],
            vec![5, 0, 0, 0, 3, 0, 4, 6, 0, 1, 15, 0, 0, 0, 0, 0],
            vec![0, 9, 1, 6, 0, 14, 0, 11, 0, 0, 2, 0, 0, 0, 10, 8],
            vec![0, 14, 0, 0, 0, 13, 9, 0, 4, 12, 11, 8, 0, 0, 2, 0],
        ];

        print_sudoku(&sudoku_16, &sudoku_16);
        let clauses = clauses_from_sudoku(&sudoku_16);
        clauses.iter().for_each(|clause| solver.add_clause(clause));
        let status = solver.solve(None);
        match status {
            Status::Sat => {
                println!("SAT");
                let result = board_from_assign(sudoku_16.len(), &solver.assigns);
                if !util::sat_model_check(&clauses, &solver.assigns) {
                    panic!("Assignments are wrong!!");
                }
                print_sudoku(&result, &sudoku_16);
            }
            Status::Unsat => {
                println!("UNSAT");
            }
            _ => {
                println!("INDETERMINATE");
            }
        }
    }
}
