pub mod solver {

    use std::{
        collections::{HashMap, HashSet, VecDeque},
        time::{Duration, Instant},
        vec,
    };
    /// A boolean variable
    pub type Var = usize;
    /// A literal is either a variable or a negation of a variable.
    /// (0, true) means x0 and (0, false) means ¬x0.
    pub type Lit = (Var, bool);
    pub trait Negation {
        fn neg(self) -> Self;
    }
    impl Negation for Lit {
        fn neg(self) -> Self {
            (self.0, !self.1)
        }
    }

    #[derive(PartialEq, Debug)]
    /// The status of a problem that solver solved.
    /// - `Sat` a solver found that a given problem is SATISFIABLE.
    /// - `Unsat` a solver found that a given problem is UNSATISFIABLE.
    /// - `Indeterminate` a solver stopped searching.
    pub enum Status {
        Sat,
        Unsat,
        Indeterminate,
    }

    #[derive(Debug, Default)]
    // A SAT Solver
    pub struct Solver {
        // the number of variables
        n: usize,
        // assignments for each variable
        pub assigns: Vec<bool>,
        // all clauses(original + learnt)
        clauses: Vec<Vec<Lit>>,
        // clauses that may be conflicted or propagated if a `lit` is false.
        watchers: HashMap<Lit, Vec<usize>>,
        // a clause index represents that a variable is forced to be assigned.
        reason: Vec<Option<usize>>,
        // decision level(0: unassigned, 1: minimum level)
        level: Vec<usize>,
        // assigned variables
        que: VecDeque<Var>,
        //the head index of `que` points unprocessed elements
        head: usize,
    }

    impl Solver {
        /// Enqueue a variable to assign a `value` to a boolean `assign`
        fn enqueue(&mut self, var: Var, assign: bool, reason: Option<usize>) {
            self.assigns[var] = assign;
            self.reason[var] = reason;
            self.level[var] = if let Some(last) = self.que.back() {
                self.level[*last]
            } else {
                1
            };
            self.que.push_back(var);
        }

        // Create a new space for one variable.
        pub fn new_var(&mut self) {
            self.n += 1;
            self.assigns.push(false);
            self.reason.push(None);
            self.level.push(0);
        }

        /// This method is only for internal usage and almost same as `add_clause`
        /// But, this method doesn't grow the size of array.
        fn add_clause_unchecked(&mut self, clause: &[Lit]) {
            assert!(clause.len() >= 2);
            let clause_idx = self.clauses.len();
            for &c in clause.iter() {
                self.watchers.entry(c).or_insert(vec![]).push(clause_idx);
            }
            self.clauses.push(clause.to_vec());
        }
        /// Add a new clause to `clauses` and watch a clause.
        /// If a variable is greater than the size of array, grow it.
        /// # Arguments
        /// * `clause` - a clause has one or some literal variables
        pub fn add_clause(&mut self, clause: &[Lit]) {
            if clause.len() == 1 {
                let c = clause[0];
                while c.0 >= self.assigns.len() {
                    self.new_var();
                }
                self.enqueue(c.0, c.1, None);
                return;
            }
            let clause_idx = self.clauses.len();
            for &c in clause.iter() {
                while c.0 >= self.assigns.len() {
                    self.new_var();
                }
                self.watchers.entry(c).or_insert(vec![]).push(clause_idx);
            }
            self.clauses.push(clause.to_vec());
        }

        /// Propagate it by all enqueued values and check conflicts.
        /// If a conflict is detected, this function returns a conflicted clause index.
        /// `None` is no conflicts.
        fn propagate(&mut self) -> Option<usize> {
            while self.head < self.que.len() {
                let p = {
                    let v = self.que[self.head];
                    self.head += 1;
                    (v, !self.assigns[v])
                };

                if let Some(watcher) = self.watchers.get(&p) {
                    'next_clause: for &cr in watcher.iter() {
                        let mut cnt = 0;
                        //let clause = &mut self.clauses[*cr];
                        let len = self.clauses[cr].len();

                        for c in 0..len {
                            let (v, sign) = self.clauses[cr][c];
                            if self.level[v] == 0 {
                                // this variable hasn't been decided yet
                                self.clauses[cr].swap(c, 0);
                                cnt += 1;
                                if cnt >= 2 {
                                    // this clause won't happan a conflict or propagation.
                                    continue 'next_clause;
                                }
                            } else if self.assigns[v] == sign {
                                // this clause is already satisfied
                                self.clauses[cr].swap(c, 0);
                                continue 'next_clause;
                            }
                        }
                        if cnt == 0 {
                            return Some(cr);
                        } else if cnt == 1 {
                            // Unit clause
                            let (var, sign) = self.clauses[cr][0];
                            debug_assert!(self.level[var] == 0);
                            // NOTE
                            // I don't know how to handle this borrowing problem. Please help me.
                            // self.enqueue(var, sign, Some(cr));

                            self.assigns[var] = sign;
                            self.reason[var] = Some(cr);
                            self.level[var] = if let Some(last) = self.que.back() {
                                self.level[*last]
                            } else {
                                1
                            };
                            self.que.push_back(var);
                        }
                    }
                }
            }
            None
        }
        /// Analyze a conflict clause and deduce a learnt clause to avoid a current conflict
        fn analyze(&mut self, mut confl: usize) {
            let mut que_tail = self.que.len() - 1;
            let mut checked_vars = HashSet::new();
            let current_level = self.level[self.que[que_tail]];

            let mut learnt_clause = vec![];
            let mut backtrack_level = 1;
            let mut same_level_cnt = 0;
            let mut skip = false;
            loop {
                for p in self.clauses[confl].iter() {
                    let (var, _) = *p;
                    debug_assert!(self.level[var] != 0);
                    if skip && var == self.que[que_tail] {
                        continue;
                    }

                    // already checked
                    if !checked_vars.insert(var) {
                        continue;
                    }
                    debug_assert!(self.level[var] <= current_level);
                    if self.level[var] < current_level {
                        learnt_clause.push(*p);
                        backtrack_level = std::cmp::max(backtrack_level, self.level[var]);
                    } else {
                        same_level_cnt += 1;
                    }
                }

                // Find the latest a value that is checked
                while !checked_vars.contains(&self.que[que_tail]) {
                    que_tail -= 1;
                }

                same_level_cnt -= 1;
                // There is no variables that are at the conflict level
                if same_level_cnt <= 0 {
                    break;
                }
                // Next
                skip = true;
                checked_vars.remove(&self.que[que_tail]);
                debug_assert_eq!(self.level[self.que[que_tail]], current_level);
                confl = self.reason[self.que[que_tail]].unwrap();
            }
            let p = self.que[que_tail];
            learnt_clause.push((p, !self.assigns[p]));

            // Cancel decisions until the level is less than equal to the backtrack level
            while let Some(p) = self.que.back() {
                if self.level[*p] > backtrack_level {
                    self.level[*p] = 0;
                    self.que.pop_back();
                } else {
                    break;
                }
            }

            // propagate it by a new learnt clause
            if learnt_clause.len() == 1 {
                debug_assert_eq!(backtrack_level, 1);
                self.enqueue(p, !self.assigns[p], None);
                self.head = self.que.len() - 1;
            } else {
                self.enqueue(p, !self.assigns[p], Some(self.clauses.len()));
                self.head = self.que.len() - 1;
                self.add_clause_unchecked(&learnt_clause);
            }
        }
        /// Create a new `Solver` struct
        ///
        /// # Arguments
        /// * `n` - The number of variable
        /// * `clauses` - All clauses that solver solves
        pub fn new(n: usize, clauses: &[Vec<Lit>]) -> Solver {
            let mut solver = Solver {
                n,
                que: VecDeque::new(),
                head: 0,
                clauses: Vec::new(),
                reason: vec![None; n],
                level: vec![0; n],
                assigns: vec![false; n],
                watchers: HashMap::new(),
            };
            for clause in clauses.iter() {
                if clause.len() == 1 {
                    solver.enqueue(clause[0].0, clause[0].1, None);
                } else {
                    solver.add_clause_unchecked(clause);
                }
            }
            solver
        }
        /// Reserve the space of a clause database
        /// # Arguments
        /// * `cla_num` - The number of clause
        pub fn reserve_clause(&mut self, cla_num: usize) {
            self.clauses.reserve(cla_num);
        }
        // Reserve the space of variables
        /// # Arguments
        /// * `var_num` - The number of variable
        pub fn reserve_variable(&mut self, var_num: usize) {
            self.que.reserve(var_num);
            self.clauses.reserve(var_num);
            self.reason.reserve(var_num);
            self.level.reserve(var_num);
            self.assigns.reserve(var_num);
        }

        /// Solve a problem and return a enum `Status`.
        /// # Arguments
        /// * `time_limit` - The time limitation for searching.
        /// Exceeding the time limit returns `Indeterminate`
        pub fn solve(&mut self, time_limit: Option<Duration>) -> Status {
            let start = Instant::now();
            loop {
                if let Some(time_limit) = time_limit {
                    if start.elapsed() > time_limit {
                        // exceed the time limit
                        return Status::Indeterminate;
                    }
                }
                if let Some(confl) = self.propagate() {
                    //Conflict
                    let current_level = self.level[*self.que.back().unwrap()];
                    if current_level == 1 {
                        return Status::Unsat;
                    }
                    self.analyze(confl);
                } else {
                    // No Conflict
                    // Select a decision variable that isn't decided yet
                    let nxt_var = self.level.iter().position(|level| *level == 0);

                    if let Some(nxt_var) = nxt_var {
                        self.enqueue(nxt_var, self.assigns[nxt_var], None);
                        self.level[nxt_var] += 1;
                    } else {
                        // all variables are selected. which means that a formula is satisfied
                        return Status::Sat;
                    }
                }
            }
        }
    }
}

// This mod contains utility functions
pub mod util {
    use super::solver::{Lit, Var};
    use std::io::BufRead;

    // CnfData is parsed form a input file
    #[derive(Debug)]
    pub struct CnfData {
        // the number of variable
        pub var_num: Option<usize>,
        // the number of clause
        pub cla_num: Option<usize>,
        // all problem clauses
        pub clauses: Vec<Vec<Lit>>,
    }
    /// Parse a DIMACAS cnf file
    /// # Arguments
    /// * `input_file` - A path of an input file name
    /// c Here is a comment.
    /// c SATISFIABLE
    /// p cnf 5 3
    /// 1 -5 4 0
    /// -1 5 3 4 0
    /// -3 -4 0
    pub fn parse_cnf(input_file: &str) -> std::io::Result<CnfData> {
        let file = std::fs::File::open(input_file)?;
        let reader = std::io::BufReader::new(file);
        let mut var_num = None;
        let mut cla_num = None;
        let mut clauses = vec![];
        for line in reader.lines() {
            let line = line?;
            let line = line.trim();

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
                .into_iter()
                .filter_map(|x| x.parse::<i32>().ok())
                .take_while(|x| *x != 0)
                .collect();

            if values.is_empty() {
                // skip an empty line
                continue;
            }
            let clause: Vec<Lit> = values
                .iter()
                .map(|&x| {
                    let d = x.abs() as Var;
                    if x > 0 {
                        (d - 1, true)
                    } else {
                        (d - 1, false)
                    }
                })
                .collect();
            clauses.push(clause);
        }
        Ok(CnfData {
            var_num,
            cla_num,
            clauses,
        })
    }

    pub fn sat_model_check(clauses: &[Vec<Lit>], assigns: &[bool]) -> bool {
        for clause in clauses.iter() {
            let mut satisfied = false;
            for lit in clause {
                if assigns[lit.0] == lit.1 {
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
}
