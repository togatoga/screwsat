pub mod solver {

    use std::{
        cell::RefCell,
        collections::{HashSet, VecDeque},
        ops::{Index, IndexMut},
        rc::{Rc, Weak},
        time::{Duration, Instant},
        vec,
    };

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
    pub struct Var(pub u32);

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
    pub struct Lit(u32);
    impl Lit {
        pub fn new(var: Var, positive: bool) -> Lit {
            Lit(if positive { 2 * var.0 } else { 2 * var.0 + 1 })
        }
        pub fn var(self) -> Var {
            Var(self.0 >> 1)
        }
        pub fn pos(&self) -> bool {
            if self.0 & 1 == 0 {
                true
            } else {
                false
            }
        }
        pub fn neg(&self) -> bool {
            !self.pos()
        }
    }
    impl From<i32> for Lit {
        fn from(x: i32) -> Self {
            assert!(x != 0);
            let d = x.abs() as u32 - 1;
            if x > 0 {
                Lit(2 * d)
            } else {
                Lit(2 * d + 1)
            }
        }
    }
    impl std::ops::Not for Lit {
        type Output = Self;
        fn not(self) -> Self::Output {
            if self.pos() {
                Lit(self.0 + 1)
            } else {
                Lit(self.0 - 1)
            }
        }
    }

    pub type Clause = Vec<Lit>;

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Clone)]
    struct CRef(Rc<RefCell<Clause>>);
    type CWRef = Weak<RefCell<Clause>>;
    impl CRef {
        fn new(clause: Clause) -> CRef {
            CRef(Rc::new(RefCell::new(clause)))
        }
    }

    #[derive(PartialEq, Debug, Copy, Clone)]
    /// The status of a problem that solver solved.
    /// - `Sat` a solver found that a given problem is SATISFIABLE.
    /// - `Unsat` a solver found that a given problem is UNSATISFIABLE.
    /// - `Indeterminate` a solver stopped searching.
    pub enum Status {
        Sat,
        Unsat,
        Indeterminate,
    }
    #[derive(PartialEq, Debug, Copy, Clone)]
    enum LitBool {
        True,
        False,
        Undef,
    }
    impl<T> Index<Var> for Vec<T> {
        type Output = T;

        fn index(&self, var: Var) -> &Self::Output {
            &self[var.0 as usize]
        }
    }
    impl<T> IndexMut<Var> for Vec<T> {
        fn index_mut(&mut self, var: Var) -> &mut Self::Output {
            &mut self[var.0 as usize]
        }
    }

    impl<T> Index<Lit> for Vec<T> {
        type Output = T;

        fn index(&self, lit: Lit) -> &Self::Output {
            &self[lit.0 as usize]
        }
    }
    impl<T> IndexMut<Lit> for Vec<T> {
        fn index_mut(&mut self, lit: Lit) -> &mut Self::Output {
            &mut self[lit.0 as usize]
        }
    }

    #[derive(Debug, Default)]
    // A SAT Solver
    pub struct Solver {
        // the number of variables
        n: usize,
        // assignments for each variable
        pub assigns: Vec<bool>,
        // original clauses
        clauses: Vec<CRef>,
        // learnt clauses
        learnts: Vec<CRef>,
        // clauses that may be conflicted or propagated if a `lit` is false.
        watchers: Vec<Vec<CWRef>>,
        // a clause index represents that a variable is forced to be assigned.
        reason: Vec<Option<CWRef>>,
        // decision level(0: unassigned, 1: minimum level)
        level: Vec<usize>,
        // assigned variables
        que: VecDeque<Lit>,
        // the head index of `que` points unprocessed elements
        head: usize,
        // the solver status. this value may be set by the functions `add_clause` and `solve`.
        pub status: Option<Status>,
    }

    impl Solver {
        fn eval(&self, lit: Lit) -> LitBool {
            if self.level[lit.var()] == 0 {
                return LitBool::Undef;
            }
            if lit.pos() {
                if self.assigns[lit.var()] {
                    LitBool::True
                } else {
                    LitBool::False
                }
            } else {
                if self.assigns[lit.var()] {
                    LitBool::False
                } else {
                    LitBool::True
                }
            }
        }
        /// Enqueue a variable to assign a `value` to a boolean `assign`
        fn enqueue(&mut self, lit: Lit, reason: Option<CRef>) {
            debug_assert!(self.level[lit.var()] == 0);
            self.assigns[lit.var()] = lit.pos();
            self.reason[lit.var()] = reason.and_then(|cr: CRef| Some(Rc::downgrade(&cr.0)));
            self.level[lit.var()] = if let Some(last) = self.que.back() {
                self.level[last.var()]
            } else {
                1
            };
            self.que.push_back(lit);
        }

        // Create a new space for one variable.
        pub fn new_var(&mut self) {
            self.n += 1;
            self.assigns.push(false);
            self.reason.push(None);
            self.level.push(0);
            // for literals
            self.watchers.push(Vec::new());
            self.watchers.push(Vec::new());
        }

        /// This method is only for internal usage and almost same as `add_clause`
        /// But, this method doesn't grow the size of array.
        fn add_clause_unchecked(&mut self, cr: CRef, learnt: bool) {
            let clause = cr.0.borrow();
            debug_assert!(clause.len() >= 2);
            //let cr = Rc::new(RefCell::new(clause));

            self.watchers[!clause[0]].push(Rc::downgrade(&cr.0));
            self.watchers[!clause[1]].push(Rc::downgrade(&cr.0));
            if learnt {
                self.learnts.push(cr.clone());
            } else {
                self.clauses.push(cr.clone());
            }
        }
        /// Add a new clause to `clauses` and watch a clause.
        /// If a variable is greater than the size of array, grow it.
        /// # Arguments
        /// * `clause` - a clause has one or some literal variables
        pub fn add_clause(&mut self, clause: &Clause) {
            // grow the space of array variables.
            clause.iter().for_each(|c| {
                while c.var().0 as usize >= self.assigns.len() {
                    self.new_var();
                }
            });

            // Simplify a clause
            let mut clause = clause.to_vec();
            clause.sort();
            let mut len = 0;
            for i in 0..clause.len() {
                let mut remove = false;
                if i >= 1 {
                    // x0 v !x0 means a clause is already satisfied.
                    // you don't need to add it.
                    if clause[i] == !clause[i - 1] {
                        return;
                    }
                    // x0 v x0 duplicated
                    if clause[i] == clause[i - 1] {
                        remove = true;
                    }
                }
                let lit = clause[i];
                //already assigned
                match self.eval(lit) {
                    LitBool::True => {
                        // a clause is already satisfied. You don't need to add it.
                        return;
                    }
                    LitBool::False => {
                        // a literal is already false. You can remove it from a clause.
                        remove = true;
                    }
                    _ => {}
                }

                if !remove {
                    clause[len] = lit;
                    len += 1;
                }
            }
            clause.truncate(len);

            if clause.is_empty() {
                // Empty clause
                self.status = Some(Status::Unsat);
            } else if clause.len() == 1 {
                // Unit Clause
                let c = clause[0];
                // already assigned
                if self.eval(c) == LitBool::False {
                    self.status = Some(Status::Unsat);
                }
                self.enqueue(c, None);
                // If the conflict happnes at the root level(decision level: 0), which means that a given problem is UNSATISFIABLE.
                if self.propagate().is_some() {
                    self.status = Some(Status::Unsat);
                }
            } else {
                debug_assert!(clause.len() >= 2);
                let l1 = clause[0];
                let l2 = clause[1];
                let cr = CRef::new(clause);

                self.watchers[!l1].push(Rc::downgrade(&cr.0));
                self.watchers[!l2].push(Rc::downgrade(&cr.0));
                self.clauses.push(cr);
            }
        }

        /// Propagate it by all enqueued values and check conflicts.
        /// If a conflict is detected, this function returns a conflicted clause index.
        /// `None` is no conflicts.
        fn propagate(&mut self) -> Option<CWRef> {
            let mut conflict = None;
            'conflict: while self.head < self.que.len() {
                let p = self.que[self.head];
                self.head += 1;
                debug_assert!(self.level[p.var()] > 0);

                let false_p = !p;
                let mut idx = 0;
                'next_clause: while idx < self.watchers[p].len() {
                    debug_assert!(idx < self.watchers[p].len());
                    let cwr = self.watchers[p][idx].clone();
                    assert!(cwr.upgrade().is_some());

                    let cr = cwr.upgrade().unwrap();
                    assert!(Rc::strong_count(&cr) == 2);
                    let mut clause = cr.borrow_mut();

                    debug_assert!(clause[0] == false_p || clause[1] == false_p);

                    // make sure that the clause[1] is the false literal.
                    if clause[0] == false_p {
                        clause.swap(0, 1);
                    }
                    let first = clause[0];
                    // already satisfied
                    if self.eval(first) == LitBool::True {
                        debug_assert!(first != clause[1]);
                        idx += 1;
                        continue 'next_clause;
                    }

                    for k in 2..clause.len() {
                        let lit = clause[k];
                        // Found a literal isn't false(true or undefined)
                        if self.eval(lit) != LitBool::False {
                            clause.swap(1, k);

                            self.watchers[p][idx] = self.watchers[p].last().unwrap().clone();
                            self.watchers[p].pop();

                            self.watchers[!clause[1]].push(cwr);
                            // NOTE
                            // Don't increase `idx` because you replace and the idx element with the last one.
                            continue 'next_clause;
                        }
                    }
                    //debug_assert_eq!(watcher[idx], cr);

                    if self.eval(first) == LitBool::False {
                        // CONFLICT
                        // a first literal(clause[0]) is false.
                        // clause[1] is a false
                        // clause[2..len] is a false

                        self.head = self.que.len();
                        conflict = Some(cwr);
                        break 'conflict;
                    } else {
                        // UNIT PROPAGATION
                        // a first literal(clause[0]) isn't assigned.
                        // clause[1] is a false
                        // clause[2..len] is a false

                        debug_assert_eq!(self.level[first.var()], 0);
                        // NOTE
                        // I don't know how to handle this borrowing problem. Please help me.
                        // self.enqueue(var, sign, Some(cr));
                        self.enqueue(first, Some(CRef(cr.clone())));
                    }
                    idx += 1;
                }
            }

            conflict
        }
        fn locked(&self, cwr: &CWRef) -> bool {
            let c = cwr.upgrade().unwrap().borrow()[0];
            if self.eval(c) == LitBool::True {
                if let Some(reason) = self.reason[c.var()].as_ref() {
                    return reason.ptr_eq(cwr);
                }
            }
            false
        }
        fn unwatch_clause(&mut self, cwr: &CWRef) {
            let clause = cwr.upgrade().unwrap();
            for idx in 0..2 {
                let p = !clause.borrow()[idx];
                let n = self.watchers[p].len();
                for i in 0..n {
                    assert!(self.watchers[p][i].upgrade().is_some());
                    if self.watchers[p][i].ptr_eq(&cwr) {
                        self.watchers[p][i] = self.watchers[p].last().unwrap().clone();
                        self.watchers[p].pop();
                        break;
                    }
                }
            }
        }
        fn reduce_learnts(&mut self) {
            self.learnts.sort_by_key(|x| x.0.borrow_mut().len());
            let mut new_size = self.learnts.len() / 2;
            let n: usize = self.learnts.len();
            for i in new_size..n {
                let cr = self.learnts[i].clone();
                let cwr = Rc::downgrade(&cr.0);
                if cr.0.borrow().len() > 2 && !self.locked(&cwr) {
                    self.unwatch_clause(&cwr);
                } else {
                    self.learnts[new_size] = cr;
                    new_size += 1;
                }
            }

            self.learnts.truncate(new_size);
        }
        /// Analyze a conflict clause and deduce a learnt clause to avoid a current conflict
        fn analyze(&mut self, confl: CWRef) {
            let mut checked_vars = HashSet::new();
            let current_level = self.level[self.que[self.que.len() - 1].var()];
            let mut learnt_clause = vec![];

            let mut same_level_cnt = 0;
            assert!(confl.upgrade().is_some());
            let clause = confl.upgrade().unwrap();
            // implication graph nodes that are start point from a conflict clause.
            for p in clause.borrow().iter() {
                let var = p.var();
                debug_assert!(self.level[var] > 0);
                // already checked
                if !checked_vars.insert(var) {
                    continue;
                }
                //debug_assert!(self.level[var] <= current_level);
                if self.level[var] < current_level {
                    learnt_clause.push(*p);
                } else {
                    same_level_cnt += 1;
                }
            }

            // Traverse an implication graph to 1-UIP(unique implication point)
            let first_uip = {
                let mut p = None;
                for &lit in self.que.iter().rev() {
                    let v = lit.var();
                    // Skip a variable that isn't checked.
                    if !checked_vars.contains(&v) {
                        continue;
                    }

                    debug_assert_eq!(self.level[v], current_level);
                    same_level_cnt -= 1;
                    // There is no variables that are at the conflict level
                    if same_level_cnt <= 0 {
                        p = Some(lit);
                        break;
                    }
                    assert!(self.reason[v].is_some());
                    let reason = self.reason[v].as_ref().unwrap();
                    assert!(reason.upgrade().is_some());
                    let clause = reason.upgrade().unwrap();
                    //debug_assert!(self.clauses[reason][0].0 == v);
                    for p in clause.borrow().iter().skip(1) {
                        let var = p.var();
                        // already checked
                        if !checked_vars.insert(var) {
                            continue;
                        }
                        debug_assert!(self.level[var] <= current_level);
                        if self.level[var] < current_level {
                            learnt_clause.push(*p);
                        } else {
                            same_level_cnt += 1;
                        }
                    }
                }
                p
            };

            // p is 1-UIP.
            let p = first_uip.unwrap();
            learnt_clause.push(!p);
            let n = learnt_clause.len();
            learnt_clause.swap(0, n - 1);
            //debug_assert!(checked_vars.len() == learnt_clause.len());

            let backtrack_level = if learnt_clause.len() == 1 {
                1
            } else {
                let mut max_idx = 1;
                let mut max_level = self.level[learnt_clause[max_idx].var()];
                for (i, lit) in learnt_clause.iter().enumerate().skip(2) {
                    if self.level[lit.var()] > max_level {
                        max_level = self.level[lit.var()];
                        max_idx = i;
                    }
                }

                learnt_clause.swap(1, max_idx);
                max_level
            };

            // Cancel decisions until the level is less than equal to the backtrack level
            while let Some(p) = self.que.back() {
                if self.level[p.var()] > backtrack_level {
                    self.level[p.var()] = 0;
                    self.que.pop_back();
                } else {
                    break;
                }
            }

            // propagate it by a new learnt clause
            if learnt_clause.len() == 1 {
                debug_assert_eq!(backtrack_level, 1);
                self.enqueue(learnt_clause[0], None);
                self.head = self.que.len() - 1;
            } else {
                let first = learnt_clause[0];
                let cr = CRef::new(learnt_clause);
                self.enqueue(first, Some(cr.clone()));
                self.head = self.que.len() - 1;
                self.add_clause_unchecked(cr, true);
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
                learnts: Vec::new(),
                reason: vec![None; n],
                level: vec![0; n],
                assigns: vec![false; n],
                watchers: vec![vec![]; 2 * n],
                status: None,
            };
            clauses.iter().for_each(|clause| {
                if clause.len() == 1 {
                    solver.enqueue(clause[0], None);
                } else {
                    let cr = CRef::new(clause.clone());
                    solver.add_clause_unchecked(cr, false);
                }
            });
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
            if let Some(status) = self.status.as_ref() {
                return *status;
            }
            let start = Instant::now();
            let mut max_learnt_clause = self.clauses.len() as f64 * 0.1;

            loop {
                if let Some(time_limit) = time_limit {
                    if start.elapsed() > time_limit {
                        // exceed the time limit
                        self.status = Some(Status::Indeterminate);
                        return Status::Indeterminate;
                    }
                }
                if let Some(confl) = self.propagate() {
                    //Conflict

                    let current_level = self.level[self.que.back().unwrap().var()];
                    if current_level == 1 {
                        self.status = Some(Status::Unsat);
                        return Status::Unsat;
                    }
                    self.analyze(confl);
                } else {
                    // No Conflict
                    //eprintln!("{} {}", max_learnt_clause, self.learnts.len());
                    if max_learnt_clause as usize <= self.learnts.len() {
                        self.reduce_learnts();
                        max_learnt_clause *= 1.1;
                    }

                    // Select a decision variable that isn't decided yet
                    let next_lit = self
                        .level
                        .iter()
                        .position(|l| *l == 0)
                        .and_then(|x| Some(Lit::new(Var(x as u32), self.assigns[x])));

                    if let Some(lit) = next_lit {
                        self.enqueue(lit, None);
                        self.level[lit.var()] += 1;
                    } else {
                        // all variables are selected. which means that a formula is satisfied
                        self.status = Some(Status::Sat);
                        return Status::Sat;
                    }
                }
            }
        }
    }
}

// This mod contains utility functions
pub mod util {
    use super::solver::{Clause, Lit};
    use std::io::BufRead;

    // CnfData is parsed form a input file
    #[derive(Debug)]
    pub struct CnfData {
        // the number of variable
        pub var_num: Option<usize>,
        // the number of clause
        pub cla_num: Option<usize>,
        // all problem clauses
        pub clauses: Vec<Clause>,
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
            let clause: Vec<Lit> = values.iter().map(|&x| Lit::from(x)).collect();
            clauses.push(clause);
        }
        Ok(CnfData {
            var_num,
            cla_num,
            clauses,
        })
    }
}
