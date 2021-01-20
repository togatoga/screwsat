pub mod solver {

    use std::{
        cell::RefCell,
        collections::VecDeque,
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
        pub fn new(var: u32, positive: bool) -> Lit {
            Lit(if positive { var << 1 } else { (var << 1) + 1 })
        }
        pub fn var(self) -> Var {
            Var(self.0 >> 1)
        }
        pub fn pos(&self) -> bool {
            self.0 & 1 == 0
        }
        pub fn neg(&self) -> bool {
            !self.pos()
        }
    }
    impl From<i32> for Lit {
        fn from(x: i32) -> Self {
            debug_assert!(x != 0);
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
            Lit(self.0 ^ 1)
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
    pub enum LitBool {
        True = 0,
        False = 1,
        Undef = 2,
    }
    impl From<i8> for LitBool {
        fn from(x: i8) -> Self {
            match x {
                0 => LitBool::True,
                1 => LitBool::False,
                _ => LitBool::Undef,
            }
        }
    }
    impl<T> Index<Var> for Vec<T> {
        type Output = T;
        #[inline]
        fn index(&self, var: Var) -> &Self::Output {
            #[cfg(feature = "unsafe")]
            unsafe {
                self.get_unchecked(var.0 as usize)
            }
            #[cfg(not(feature = "unsafe"))]
            &self[var.0 as usize]
        }
    }
    impl<T> IndexMut<Var> for Vec<T> {
        #[inline]
        fn index_mut(&mut self, var: Var) -> &mut Self::Output {
            #[cfg(feature = "unsafe")]
            unsafe {
                self.get_unchecked_mut(var.0 as usize)
            }
            #[cfg(not(feature = "unsafe"))]
            &mut self[var.0 as usize]
        }
    }

    impl<T> Index<Lit> for Vec<T> {
        type Output = T;
        #[inline]
        fn index(&self, lit: Lit) -> &Self::Output {
            #[cfg(feature = "unsafe")]
            unsafe {
                &self.get_unchecked(lit.0 as usize)
            }
            #[cfg(not(feature = "unsafe"))]
            &self[lit.0 as usize]
        }
    }
    impl<T> IndexMut<Lit> for Vec<T> {
        #[inline]
        fn index_mut(&mut self, lit: Lit) -> &mut Self::Output {
            #[cfg(feature = "unsafe")]
            unsafe {
                self.get_unchecked_mut(lit.0 as usize)
            }
            #[cfg(not(feature = "unsafe"))]
            &mut self[lit.0 as usize]
        }
    }

    #[derive(Debug, Clone)]
    struct Heap {
        heap: Vec<Var>,
        indices: Vec<Option<usize>>,
        activity: Vec<f64>,
        bump_inc: f64,
    }
    impl Default for Heap {
        fn default() -> Self {
            Heap {
                heap: Vec::default(),
                indices: Vec::default(),
                activity: Vec::default(),
                bump_inc: 1.0,
            }
        }
    }
    impl Heap {
        pub fn new(n: usize, bump_inc: f64) -> Heap {
            Heap {
                heap: (0..n).map(|x| Var(x as u32)).collect(),
                indices: (0..n).map(Some).collect(),
                activity: vec![0.0; n],
                bump_inc,
            }
        }

        fn gt(&self, left: Var, right: Var) -> bool {
            self.activity[left] > self.activity[right]
        }
        #[allow(dead_code)]
        fn top(self) -> Option<Var> {
            if self.heap.is_empty() {
                return None;
            }
            Some(self.heap[0])
        }
        pub fn decay_inc(&mut self) {
            self.bump_inc *= 1.0 / 0.95;
        }
        pub fn bump_activity(&mut self, v: Var) {
            self.activity[v] += self.bump_inc;

            if self.activity[v] >= 1e100 {
                for i in 0..self.activity.len() {
                    self.activity[i] *= 1e-100;
                }
                self.bump_inc *= 1e-100;
            }
            if self.in_heap(v) {
                let idx = self.indices[v].unwrap();
                self.up(idx);
            }
        }
        #[allow(dead_code)]
        fn update(&mut self, v: Var) {
            if !self.in_heap(v) {
                self.push(v);
            } else {
                let idx = self.indices[v].unwrap();
                self.up(idx);
                self.down(idx);
            }
        }
        fn up(&mut self, i: usize) {
            if i == 0 {
                return;
            }
            let mut idx = i;
            let x = self.heap[idx];
            let mut par = (idx - 1) >> 1;
            loop {
                if !self.gt(x, self.heap[par]) {
                    break;
                }
                self.heap[idx] = self.heap[par];
                self.indices[self.heap[par]] = Some(idx);
                idx = par;
                if idx == 0 {
                    break;
                }
                par = (par - 1) >> 1;
            }
            self.heap[idx] = x;
            self.indices[x] = Some(idx);
        }

        fn pop(&mut self) -> Option<Var> {
            if self.heap.is_empty() {
                return None;
            }
            let x = self.heap[0];
            self.indices[x] = None;
            if self.heap.len() > 1 {
                self.heap[0] = *self.heap.last().unwrap();
                self.indices[self.heap[0]] = Some(0);
            }
            self.heap.pop();
            if self.heap.len() > 1 {
                self.down(0);
            }
            Some(x)
        }

        fn down(&mut self, i: usize) {
            let x = self.heap[i];
            let mut idx = i;
            while 2 * idx + 1 < self.heap.len() {
                let left = 2 * idx + 1;
                let right = left + 1;
                let child = if right < self.heap.len() && self.gt(self.heap[right], self.heap[left])
                {
                    right
                } else {
                    left
                };
                if self.gt(self.heap[child], x) {
                    self.heap[idx] = self.heap[child];
                    self.indices[self.heap[idx]] = Some(idx);
                    idx = child;
                } else {
                    break;
                }
            }
            self.heap[idx] = x;
            self.indices[x] = Some(idx);
        }

        fn push(&mut self, v: Var) {
            if self.in_heap(v) {
                return;
            }
            while (v.0 as usize) >= self.indices.len() {
                self.indices.push(None);
                self.activity.push(0.0);
            }
            self.indices[v] = Some(self.heap.len());
            self.heap.push(v);
            self.up(self.indices[v].unwrap());
        }

        fn in_heap(&mut self, v: Var) -> bool {
            (v.0 as usize) < self.indices.len() && self.indices[v].is_some()
        }
    }

    #[derive(Debug, Default)]
    // A SAT Solver
    pub struct Solver {
        // the number of variables
        n: usize,
        // assignments for each variable
        pub assigns: Vec<LitBool>,
        polarity: Vec<bool>,
        // original clauses
        clauses: Vec<CRef>,
        // learnt clauses
        learnts: Vec<CRef>,
        // clauses that may be conflicted or propagated if a `lit` is false.
        watchers: Vec<Vec<CWRef>>,
        // a clause index represents that a variable is forced to be assigned.
        reason: Vec<Option<CWRef>>,
        seen: Vec<bool>,
        ccmin_stack: VecDeque<Lit>,
        ccmin_clear: Vec<Lit>,
        // decision level(0: unassigned, 1: minimum level)
        level: Vec<usize>,
        // assigned variables
        que: VecDeque<Lit>,
        // the head index of `que` points unprocessed elements
        head: usize,
        // the solver status. this value may be set by the functions `add_clause` and `solve`.
        pub status: Option<Status>,
        order_heap: Heap,
        skip_simplify: bool,
    }

    impl Solver {
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
                seen: vec![false; n],
                ccmin_stack: VecDeque::new(),
                ccmin_clear: Vec::new(),
                assigns: vec![LitBool::Undef; n],
                polarity: vec![false; n],
                order_heap: Heap::new(n, 1.0),
                watchers: vec![vec![]; 2 * n],
                status: None,
                skip_simplify: false,
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
        fn eval(&self, lit: Lit) -> LitBool {
            LitBool::from(self.assigns[lit.var()] as i8 ^ lit.neg() as i8)
        }
        /// Enqueue a variable to assign a `value` to a boolean `assign`
        fn enqueue(&mut self, lit: Lit, reason: Option<CRef>) {
            debug_assert!(self.level[lit.var()] == 0);
            self.assigns[lit.var()] = LitBool::from(lit.neg() as i8);

            self.reason[lit.var()] = reason.map(|cr: CRef| Rc::downgrade(&cr.0));
            self.level[lit.var()] = if let Some(last) = self.que.back() {
                self.level[last.var()]
            } else {
                1
            };
            self.que.push_back(lit);
        }

        // Create a new space for one variable.
        pub fn new_var(&mut self) {
            let v = Var(self.n as u32);
            self.n += 1;
            self.assigns.push(LitBool::Undef);
            self.polarity.push(false);
            self.reason.push(None);
            self.level.push(0);
            self.order_heap.push(v);
            self.seen.push(false);
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
        pub fn add_clause(&mut self, clause: &[Lit]) {
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

                let mut idx = 0;

                'next_clause: while idx < self.watchers[p].len() {
                    let m = self.watchers[p].len();
                    debug_assert!(idx < m);
                    let cwr = self.watchers[p][idx].clone();
                    debug_assert!(cwr.upgrade().is_some());

                    let cr = cwr.upgrade().unwrap();
                    debug_assert!(Rc::strong_count(&cr) == 2);
                    let mut clause = cr.borrow_mut();

                    debug_assert!(clause[0] == !p || clause[1] == !p);

                    // make sure that the clause[1] is the false literal.
                    if clause[0] == !p {
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

                            self.watchers[p].swap(idx, m - 1);
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
            let mut cnt = 0;
            for idx in 0..2 {
                let p = !clause.borrow()[idx];
                let n = self.watchers[p].len();
                for i in 0..n {
                    if self.watchers[p][i].ptr_eq(&cwr) {
                        self.watchers[p].swap(i, n - 1);
                        self.watchers[p].pop();
                        cnt += 1;
                        break;
                    }
                }
            }
            debug_assert!(cnt == 2);
        }
        fn reduce_learnts(&mut self) {
            self.learnts.sort_by_key(|x| x.0.borrow_mut().len());
            let mut new_size = self.learnts.len() / 2;
            let m = new_size;
            let n: usize = self.learnts.len();
            for i in m..n {
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

        fn pop_queue_until(&mut self, backtrack_level: usize) {
            while let Some(p) = self.que.back() {
                if self.level[p.var()] > backtrack_level {
                    if !self.order_heap.in_heap(p.var()) {
                        self.order_heap.push(p.var());
                    }
                    self.polarity[p.var()] = match self.assigns[p.var()] {
                        LitBool::True => true,
                        _ => false,
                    };
                    self.assigns[p.var()] = LitBool::Undef;
                    self.reason[p.var()] = None;
                    self.level[p.var()] = 0;
                    self.que.pop_back();
                } else {
                    break;
                }
            }
            if self.que.is_empty() {
                self.head = 0;
            } else {
                self.head = self.que.len() - 1;
            }
        }

        fn simplify(&mut self) {
            {
                let n: usize = self.learnts.len();
                let mut new_size = 0;
                for i in 0..n {
                    let cr = self.learnts[i].clone();
                    let clause = cr.0.borrow();
                    let mut satisfied = false;
                    for &lit in clause.iter() {
                        if self.eval(lit) == LitBool::True {
                            let cwr = Rc::downgrade(&cr.0);
                            self.unwatch_clause(&cwr);
                            if self.locked(&cwr) {
                                debug_assert!(self.reason[clause[0].var()].is_some());
                                self.reason[clause[0].var()] = None;
                            }
                            satisfied = true;
                            break;
                        }
                    }
                    drop(clause);
                    if !satisfied {
                        self.learnts[new_size] = cr;
                        new_size += 1;
                    }
                }
                self.learnts.truncate(new_size);
            }
            {
                let n: usize = self.clauses.len();
                let mut new_size = 0;
                for i in 0..n {
                    let cr = self.clauses[i].clone();
                    let clause = cr.0.borrow();
                    let mut satisfied = false;
                    for &lit in clause.iter() {
                        if self.eval(lit) == LitBool::True {
                            let cwr = Rc::downgrade(&cr.0);
                            self.unwatch_clause(&cwr);
                            if self.locked(&cwr) {
                                debug_assert!(self.reason[clause[0].var()].is_some());
                                self.reason[clause[0].var()] = None;
                            }
                            satisfied = true;
                            break;
                        }
                    }
                    drop(clause);
                    if !satisfied {
                        self.clauses[new_size] = cr;
                        new_size += 1;
                    }
                }
                self.clauses.truncate(new_size);
            }
        }
        fn lit_redundant(&mut self, lit: Lit) -> bool {
            // Check whether a literal can reach a decision variable or unit clause literal.
            // Self-subsume
            self.ccmin_stack.clear();
            let top = self.ccmin_clear.len();
            self.ccmin_stack.push_back(lit);
            while let Some(x) = self.ccmin_stack.pop_back() {
                let cwr = self.reason[x.var()].as_ref().unwrap();
                let cr = cwr.upgrade().unwrap();
                let clause = cr.borrow();
                debug_assert!(clause[0] == !x);
                for c in clause.iter().skip(1) {
                    if !self.seen[c.var()] && self.level[c.var()] > 1 {
                        if self.reason[c.var()].is_some() {
                            self.seen[c.var()] = true;
                            self.ccmin_stack.push_back(*c);
                            self.ccmin_clear.push(*c);
                        } else {
                            // A 'c' is a decision variable or unit clause literal.
                            // which means a "lit" isn't redundant
                            for lit in self.ccmin_clear.iter().skip(top) {
                                self.seen[lit.var()] = false;
                            }
                            self.ccmin_clear.truncate(top);
                            return false;
                        }
                    }
                }
            }
            return true;
        }
        fn minimize_conflict_clause(&mut self, learnt_clause: &mut Clause) {
            debug_assert!(self.ccmin_stack.is_empty());
            debug_assert!(self.ccmin_clear.is_empty());
            // Simplify conflict clauses
            let n: usize = learnt_clause.len();
            let mut new_size = 1;
            for i in 1..n {
                let x = learnt_clause[i].var();
                let mut redundant = false;

                // Traverse a conflict literal to check wheter a literal is redundant.
                if self.reason[x].is_some() {
                    redundant = self.lit_redundant(learnt_clause[i]);
                }

                if !redundant {
                    learnt_clause[new_size] = learnt_clause[i];
                    new_size += 1;
                }
            }
            // clear all
            for lit in self.ccmin_clear.iter() {
                self.seen[lit.var()] = false;
            }
            self.ccmin_stack.clear();
            self.ccmin_clear.clear();
            debug_assert!(self.ccmin_stack.is_empty());
            debug_assert!(self.ccmin_clear.is_empty());
            learnt_clause.truncate(new_size);
        }
        /// Analyze a conflict clause and deduce a learnt clause to avoid a current conflict
        fn analyze(&mut self, confl: CWRef) {
            // seen must be clear
            debug_assert!(self.seen.iter().all(|&x| !x));

            let current_level = self.level[self.que[self.que.len() - 1].var()];
            let mut learnt_clause = vec![];

            let mut same_level_cnt = 0;
            debug_assert!(confl.upgrade().is_some());
            let clause = confl.upgrade().unwrap();
            // implication graph nodes that are start point from a conflict clause.
            for p in clause.borrow().iter() {
                let var = p.var();
                debug_assert!(self.level[var] > 0);
                self.order_heap.bump_activity(var);
                // already checked
                self.seen[var] = true;

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
                    if !self.seen[v] {
                        continue;
                    }
                    self.seen[v] = false;
                    self.order_heap.bump_activity(v);
                    debug_assert_eq!(self.level[v], current_level);
                    same_level_cnt -= 1;
                    // There is no variables that are at the conflict level
                    if same_level_cnt <= 0 {
                        p = Some(lit);
                        break;
                    }

                    debug_assert!(self.reason[v].is_some());
                    let reason = self.reason[v].as_ref().unwrap();
                    debug_assert!(reason.upgrade().is_some());
                    let clause = reason.upgrade().unwrap();
                    for p in clause.borrow().iter().skip(1) {
                        let var = p.var();
                        // already checked
                        if self.seen[var] {
                            continue;
                        }
                        self.seen[var] = true;
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
            {
                let p = first_uip.unwrap();
                learnt_clause.push(!p);
                let n = learnt_clause.len();
                learnt_clause.swap(0, n - 1);
            }

            let analyze_clear = learnt_clause.clone();
            self.minimize_conflict_clause(&mut learnt_clause);

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
            self.pop_queue_until(backtrack_level);

            // propagate it by a new learnt clause
            if learnt_clause.len() == 1 {
                debug_assert_eq!(backtrack_level, 1);
                self.skip_simplify = false;
                self.enqueue(learnt_clause[0], None);
            } else {
                let first = learnt_clause[0];
                let cr = CRef::new(learnt_clause);
                self.enqueue(first, Some(cr.clone()));
                self.add_clause_unchecked(cr, true);
            }

            // Clear seen
            for lit in analyze_clear {
                self.seen[lit.var()] = false;
            }
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
            let mut max_learnt_clause = self.clauses.len() as f64 * 0.3;
            let mut conflict_cnt = 0;
            let mut restart_limit = 100.0;

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
                    conflict_cnt += 1;
                    self.analyze(confl);
                    self.order_heap.decay_inc();
                } else {
                    // No Conflict
                    if conflict_cnt as f64 >= restart_limit {
                        restart_limit *= 1.1;
                        self.pop_queue_until(1);
                        if !self.skip_simplify {
                            self.simplify();
                            self.skip_simplify = true;
                        }
                    }

                    if max_learnt_clause as usize <= self.learnts.len() {
                        self.reduce_learnts();
                        max_learnt_clause *= 1.1;
                    }

                    // Select a decision variable that isn't decided yet
                    loop {
                        if let Some(v) = self.order_heap.pop() {
                            if self.level[v] != 0 {
                                continue;
                            }

                            let lit = Lit::new(v.0, self.polarity[v]);
                            self.enqueue(lit, None);
                            self.level[lit.var()] += 1;
                            break;
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
    pub fn parse_cnf<R: std::io::Read>(input: R) -> std::io::Result<CnfData> {
        let reader = std::io::BufReader::new(input);
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
