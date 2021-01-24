pub mod solver {

    use std::{
        collections::HashMap,
        ops::{Deref, DerefMut, Index, IndexMut},
        time::{Duration, Instant},
        vec,
    };

    const TOP_LEVEL: usize = 0;
    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
    pub struct Var(pub u32);
    impl Var {
        #[allow(dead_code)]
        fn from_idx(x: usize) -> Var {
            Var(x as u32)
        }
    }

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
    pub struct Lit(u32);
    impl Lit {
        pub fn new(var: u32, positive: bool) -> Lit {
            Lit(if positive { var << 1 } else { (var << 1) + 1 })
        }
        #[inline]
        pub fn var(self) -> Var {
            Var(self.0 >> 1)
        }
        #[inline]
        pub fn pos(&self) -> bool {
            self.0 & 1 == 0
        }
        #[inline]
        pub fn neg(&self) -> bool {
            self.0 & 1 != 0
        }
    }
    impl From<i32> for Lit {
        #[inline]
        fn from(x: i32) -> Self {
            debug_assert!(x != 0);
            let d = x.abs() as u32 - 1;
            if x > 0 {
                Lit(d << 1)
            } else {
                Lit((d << 1) + 1)
            }
        }
    }
    impl std::ops::Not for Lit {
        type Output = Self;
        #[inline]
        fn not(self) -> Self::Output {
            Lit(self.0 ^ 1)
        }
    }

    // Clause //

    #[derive(Debug, Default, PartialEq, PartialOrd)]
    pub struct Clause {
        data: Vec<Lit>,
        activity: f32,
        learnt: bool,
        free: bool, // will be deleted
    }
    impl Clause {
        fn new(clause: &[Lit]) -> Clause {
            Clause {
                data: clause.to_vec(),
                activity: 0.0,
                learnt: false,
                free: false,
            }
        }
        fn with_learnt(mut self, learnt: bool) -> Clause {
            self.learnt = learnt;
            self
        }
        fn swap(&mut self, x: usize, y: usize) {
            self.data.swap(x, y);
        }
        fn len(&self) -> usize {
            self.data.len()
        }
        fn activity(&self) -> f32 {
            self.activity
        }
        fn learnt(&self) -> bool {
            self.learnt
        }
        fn byte(&self) -> usize {
            std::mem::size_of::<Lit>() * self.data.capacity() + std::mem::size_of::<Clause>()
        }
        #[allow(dead_code)]
        fn truncate(&mut self, len: usize) {
            self.data.truncate(len);
        }
    }

    impl Deref for Clause {
        type Target = [Lit];
        #[inline]
        fn deref(&self) -> &Self::Target {
            &self.data
        }
    }

    impl DerefMut for Clause {
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.data
        }
    }

    impl Index<usize> for Clause {
        type Output = Lit;
        #[inline]
        fn index(&self, idx: usize) -> &Self::Output {
            &self.data[idx]
        }
    }
    impl IndexMut<usize> for Clause {
        #[inline]
        fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
            &mut self.data[idx]
        }
    }

    impl From<Vec<Lit>> for Clause {
        fn from(lits: Vec<Lit>) -> Self {
            Clause::new(&lits)
        }
    }

    // Clause //

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
    struct CRef(usize);
    #[derive(Debug)]
    struct ClauseDB {
        // original
        clauses: Vec<CRef>,
        // learnts
        learnts: Vec<CRef>,
        db: Vec<Clause>,
        clause_inc: f32,
        total: usize,
        wasted: usize,
    }

    impl Default for ClauseDB {
        fn default() -> Self {
            let mut clause = ClauseDB::new();
            clause.clause_inc = 1.0;
            clause
        }
    }

    impl Deref for ClauseDB {
        type Target = [Clause];
        #[inline]
        fn deref(&self) -> &Self::Target {
            &self.db
        }
    }

    impl DerefMut for ClauseDB {
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.db
        }
    }

    impl Index<CRef> for ClauseDB {
        type Output = Clause;
        #[inline]
        fn index(&self, cref: CRef) -> &Self::Output {
            &self.db[cref.0]
        }
    }
    impl IndexMut<CRef> for ClauseDB {
        #[inline]
        fn index_mut(&mut self, cref: CRef) -> &mut Self::Output {
            &mut self.db[cref.0]
        }
    }

    impl ClauseDB {
        pub fn new() -> ClauseDB {
            ClauseDB {
                clauses: Vec::new(),
                learnts: Vec::new(),
                clause_inc: 0.0,
                db: Vec::new(),
                total: 0,
                wasted: 0,
            }
        }
        fn alloc(&self) -> CRef {
            CRef(self.db.len())
        }
        fn free(&mut self, cr: CRef) {
            debug_assert!(!self[cr].free);
            self.wasted += self[cr].byte();
            self[cr].free = true;
        }
        #[allow(dead_code)]
        fn wasted(&self) -> usize {
            self.wasted
        }
        #[allow(dead_code)]
        fn total(&self) -> usize {
            self.total
        }
        #[allow(dead_code)]
        fn get(&self, cr: CRef) -> &Clause {
            &self[cr]
        }
        #[allow(dead_code)]
        fn get_mut(&mut self, cr: CRef) -> &mut Clause {
            &mut self[cr]
        }

        fn bump_activity(&mut self, cr: CRef) {
            debug_assert!(self[cr].learnt());
            debug_assert!(self.clause_inc >= 0.0);
            self[cr].activity += self.clause_inc;
            if self[cr].activity() > 1e20 {
                // Rescale
                let n: usize = self.learnts.len();
                for i in 0..n {
                    let x = self.learnts[i];
                    let mut clause = &mut self[x];
                    debug_assert!(clause.learnt());
                    clause.activity *= 1e-20;
                }

                self.clause_inc *= 1e-20;
            }
        }

        fn decay_inc(&mut self) {
            self.clause_inc *= 1.0 / 0.999;
        }

        pub fn push(&mut self, lits: &[Lit], learnt: bool) -> CRef {
            let cref = self.alloc();
            if learnt {
                self.learnts.push(cref);
            } else {
                self.clauses.push(cref);
            }
            let clause = Clause::new(lits).with_learnt(learnt);
            self.total += clause.byte();
            self.db.push(clause);
            cref
        }

        fn need_collect_garbage(&mut self) -> bool {
            self.wasted() * 10 > self.total() * 2
        }

        fn collect_garbage_if_needed(
            &mut self,
            watchers: &mut Vec<Vec<Watcher>>,
            reason: &mut Vec<Option<CRef>>,
            trail: &mut Vec<Lit>,
        ) {
            if self.need_collect_garbage() {
                self.collect_garbage(watchers, reason, trail);
            }
        }
        fn collect_garbage(
            &mut self,
            watchers: &mut Vec<Vec<Watcher>>,
            reason: &mut Vec<Option<CRef>>,
            trail: &mut Vec<Lit>,
        ) {
            // assumed that Watcher doesn't have freeded CRef

            let mut map = HashMap::new();
            //cref

            self.wasted = 0;
            self.total = 0;
            for (cr, clause) in self.db.iter().enumerate() {
                if !clause.free {
                    map.insert(CRef(cr), CRef(map.len()));
                    self.total += clause.byte();
                }
            }
            // Watchers
            for watcher in watchers.iter_mut() {
                for w in watcher.iter_mut() {
                    debug_assert!(!self[w.cref].free);
                    w.cref = *map.get(&w.cref).unwrap();
                }
            }
            // Reasons
            for lit in trail.iter() {
                let v = lit.var();
                reason[v] = reason[v].map(|cr| *map.get(&cr).unwrap());
            }

            // Original
            for cr in self.clauses.iter_mut() {
                debug_assert!(!self.db[cr.0].free);
                *cr = *map.get(cr).unwrap();
            }

            // Learnts
            for cr in self.learnts.iter_mut() {
                debug_assert!(!self.db[cr.0].free);
                *cr = *map.get(cr).unwrap();
            }

            // remove all freeded clauses
            self.db.retain(|c| !c.free);
            assert!(self.db.len() == map.len());
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
        #[inline]
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
                let idx = self.indices[v].expect("No index");
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
            self.up(self.indices[v].expect("No index"));
        }

        fn in_heap(&mut self, v: Var) -> bool {
            (v.0 as usize) < self.indices.len() && self.indices[v].is_some()
        }
    }

    #[derive(Debug, Default)]
    struct Analayzer {
        seen: Vec<bool>,
        ccmin_stack: Vec<CRef>,
        ccmin_clear: Vec<Lit>,
        analyze_toclear: Vec<Lit>,
        learnt_clause: Vec<Lit>,
    }

    impl Analayzer {
        fn new(n: usize) -> Analayzer {
            Analayzer {
                seen: vec![false; n],
                ccmin_stack: Vec::new(),
                ccmin_clear: Vec::new(),
                learnt_clause: Vec::new(),
                analyze_toclear: Vec::new(),
            }
        }
    }

    /// The assignment data structure
    #[derive(Debug, Default)]
    struct AssignTrail {
        /// Assignment stack; stores all assigments made in the order they were made.
        stack: Vec<Lit>,
        /// Separator indices for different decision levels in `trail`.
        stack_limit: Vec<usize>,
        /// Head of the `trail`.
        peek_head: usize,
    }
    impl AssignTrail {
        fn new() -> AssignTrail {
            AssignTrail {
                stack: Vec::new(),
                stack_limit: Vec::new(),
                peek_head: 0,
            }
        }
        fn new_descion_level(&mut self) {
            self.stack_limit.push(self.stack.len());
        }
        #[inline]
        fn decision_level(&self) -> usize {
            self.stack_limit.len()
        }
        #[inline]
        fn peekable(&self) -> bool {
            self.peek_head < self.stack.len()
        }
        #[inline]
        fn peek(&self) -> Lit {
            self.stack[self.peek_head]
        }
        #[inline]
        fn advance(&mut self) {
            self.peek_head += 1;
        }
        fn push(&mut self, x: Lit) {
            self.stack.push(x);
        }
    }

    #[derive(Debug, Default)]
    struct VarData {
        /// assignments for each variable
        assigns: Vec<LitBool>,
        polarity: Vec<bool>,
        /// decision level(0: minimumlevel)
        level: Vec<usize>,
        // a clause that CRef points make a variable forced to be assigned
        reason: Vec<Option<CRef>>,
        trail: AssignTrail,
    }

    impl VarData {
        fn new(n: usize) -> VarData {
            VarData {
                assigns: vec![LitBool::Undef; n],
                polarity: vec![false; n],
                level: vec![TOP_LEVEL; n],
                reason: vec![None; n],
                trail: AssignTrail::new(),
            }
        }
        fn assign(&mut self, var: Var, lb: LitBool, level: usize, reason: Option<CRef>) {
            self.assigns[var] = lb;
            self.level[var] = level;
            self.reason[var] = reason;
        }
        fn level(&self, v: Var) -> usize {
            self.level[v]
        }
        #[inline]
        fn eval(&self, lit: Lit) -> LitBool {
            LitBool::from(self.assigns[lit.var()] as i8 ^ lit.neg() as i8)
        }

        fn num_assings(&self) -> usize {
            self.trail.stack.len()
        }

        /// Enqueue a variable to assign a `value` to a boolean `assign`
        fn enqueue(&mut self, lit: Lit, reason: Option<CRef>) {
            debug_assert!(self.eval(lit) == LitBool::Undef);

            self.assign(
                lit.var(),
                LitBool::from(lit.neg() as i8),
                self.trail.decision_level(),
                reason,
            );
            self.trail.push(lit);
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct RestartStrategy {
        /// The initial restart limit. (default 100)
        first: i32,
        /// The factor with which the restart limit is multiplied in each restart. (default 1.5)
        inc: f64,
    }

    impl Default for RestartStrategy {
        fn default() -> Self {
            RestartStrategy {
                first: 100,
                inc: 2.0,
            }
        }
    }

    impl RestartStrategy {
        fn luby(&mut self, mut x: i32) -> f64 {
            // Find the finite subsequence that contains index 'x', and the
            // size of that subsequence:
            let mut size = 1;
            let mut seq = 0;
            while size < x + 1 {
                seq += 1;
                size = 2 * size + 1;
            }

            while size - 1 != x {
                size = (size - 1) >> 1;
                seq -= 1;
                x %= size;
            }
            f64::powi(self.inc, seq) * self.first as f64
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct LearntSizeStrategy {
        /// The intitial limit for learnt clauses is a factor of the original clauses. (default 1 / 3)
        factor: f64,
        /// The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
        inc: f64,
        /// (default 1.5)
        adjust_inc: f64,
        adjust_start_confl: i32,
        adjust_confl: f64,

        adjust_cnt: i32,
        max_learnts: f64,
    }

    impl Default for LearntSizeStrategy {
        fn default() -> Self {
            LearntSizeStrategy {
                factor: 1.0 / 3.0,
                inc: 1.1,
                adjust_start_confl: 100,
                adjust_inc: 1.5,
                adjust_cnt: 0,
                adjust_confl: 0.0,
                max_learnts: 0.0,
            }
        }
    }

    impl LearntSizeStrategy {
        fn init(&mut self, num_clauses: usize) {
            self.max_learnts = num_clauses as f64 * self.factor;
            self.adjust_confl = self.adjust_start_confl as f64;
            self.reset_adjust_cnt();
        }
        fn dec_adjust_cnt(&mut self) {
            self.adjust_cnt -= 1;
        }
        fn adjust_if_needed(&mut self) {
            if self.adjust_cnt <= 0 {
                self.adjust();
            }
        }
        fn reset_adjust_cnt(&mut self) {
            self.adjust_cnt = self.adjust_confl as i32;
        }
        fn adjust(&mut self) {
            self.adjust_confl *= self.adjust_inc;
            self.reset_adjust_cnt();
            self.max_learnts *= self.inc;
        }
    }

    #[derive(Debug, Default, Clone, Copy)]
    struct Watcher {
        cref: CRef,
        blocker: Lit,
    }
    impl Watcher {
        fn new(cref: CRef, blocker: Lit) -> Watcher {
            Watcher { cref, blocker }
        }
    }
    #[derive(Debug, Default, Clone, Copy)]
    struct SimplifyDB {
        /// Number of top-level assignments since last execution of 'simplify()'.
        simp_db_assigns: i32,
    }

    #[derive(Debug, Default)]
    // A SAT Solver
    pub struct Solver {
        // the number of variables
        n: usize,
        // clause data base(original + learnt)
        db: ClauseDB,
        // clauses that may be conflicted or propagated if a `lit` is false.
        watchers: Vec<Vec<Watcher>>,
        // conflict analyzer
        analyzer: Analayzer,
        // variable data
        vardata: VarData,
        order_heap: Heap,

        restart_strat: RestartStrategy,
        learnt_size_start: LearntSizeStrategy,

        simplify_db: SimplifyDB,
        // the model of assigns.
        pub models: Vec<LitBool>,
        // the solver status. this value may be set by the functions `add_clause` and `solve`.
        pub status: Option<Status>,
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
                db: ClauseDB::new(),
                analyzer: Analayzer::new(n),
                vardata: VarData::new(n),
                order_heap: Heap::new(n, 1.0),
                restart_strat: RestartStrategy::default(),
                learnt_size_start: LearntSizeStrategy::default(),
                simplify_db: SimplifyDB::default(),
                watchers: vec![vec![]; 2 * n],
                status: None,
                models: vec![LitBool::Undef; n],
            };
            clauses.iter().for_each(|clause| {
                if clause.len() == 1 {
                    solver.vardata.enqueue(clause[0], None);
                } else {
                    solver.add_clause(clause);
                }
            });
            solver
        }

        // Create a new space for one variable.
        pub fn new_var(&mut self) {
            let v = Var(self.n as u32);
            self.n += 1;
            self.vardata.assigns.push(LitBool::Undef);
            self.vardata.polarity.push(false);
            self.vardata.reason.push(None);
            self.vardata.level.push(TOP_LEVEL);
            self.order_heap.push(v);
            self.analyzer.seen.push(false);
            self.models.push(LitBool::Undef);
            // for literals
            self.watchers.push(Vec::new());
            self.watchers.push(Vec::new());
        }

        /// This method is only for internal usage and almost same as `add_clause`
        /// But, this method doesn't grow the size of array.
        fn add_clause_db(&mut self, lits: &[Lit], learnt: bool) -> CRef {
            let cref = self.db.push(lits, learnt);
            debug_assert!(lits.len() >= 2);

            self.watchers[!lits[0]].push(Watcher::new(cref, lits[1]));
            self.watchers[!lits[1]].push(Watcher::new(cref, lits[0]));
            cref
        }
        /// Add a new clause to `clauses` and watch a clause.
        /// If a variable is greater than the size of array, grow it.
        /// # Arguments
        /// * `clause` - a clause has one or some literal variables
        pub fn add_clause(&mut self, clause: &[Lit]) {
            debug_assert!(self.vardata.trail.decision_level() == TOP_LEVEL);
            // grow the space of array variables.
            clause.iter().for_each(|c| {
                while c.var().0 as usize >= self.vardata.assigns.len() {
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
                match self.vardata.eval(lit) {
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
                if self.vardata.eval(c) == LitBool::False {
                    self.status = Some(Status::Unsat);
                }
                self.vardata.enqueue(c, None);
                // If the conflict happnes at the root level(decision level: 0), which means that a given problem is UNSATISFIABLE.
                if self.propagate().is_some() {
                    self.status = Some(Status::Unsat);
                }
            } else {
                debug_assert!(clause.len() >= 2);
                let l1 = clause[0];
                let l2 = clause[1];
                let cref = self.db.push(&clause, false);

                self.watchers[!l1].push(Watcher::new(cref, l2));
                self.watchers[!l2].push(Watcher::new(cref, l1));
            }
        }

        /// Propagate it by all enqueued values and check conflicts.
        /// If a conflict is detected, this function returns a conflicted clause index.
        /// `None` is no conflicts.
        fn propagate(&mut self) -> Option<CRef> {
            let mut conflict = None;
            'conflict: while self.vardata.trail.peekable() {
                let p = self.vardata.trail.peek();
                self.vardata.trail.advance();
                debug_assert!(self.vardata.assigns[p.var()] != LitBool::Undef);

                let mut idx = 0;
                let watchers_ptr = &mut self.watchers as *mut Vec<Vec<Watcher>>;
                let ws = &mut self.watchers[p];
                'next_clause: while idx < ws.len() {
                    let blocker = ws[idx].blocker;
                    let cr = ws[idx].cref;
                    if self.vardata.eval(blocker) == LitBool::True {
                        idx += 1;
                        continue;
                    }

                    let clause = &mut self.db[cr] as *mut Clause;
                    unsafe {
                        debug_assert!(!(*clause).free);
                        debug_assert!((*clause)[0] == !p || (*clause)[1] == !p);

                        // make sure that the clause[1] is the false literal.
                        if (*clause)[0] == !p {
                            (*clause).swap(0, 1);
                        }
                        let first = (*clause)[0];
                        let w = Watcher::new(cr, first);
                        // already satisfied
                        if first != blocker && self.vardata.eval(first) == LitBool::True {
                            debug_assert!(first != (*clause)[1]);
                            ws[idx] = w;
                            idx += 1;
                            continue 'next_clause;
                        }

                        for k in 2..(*clause).len() {
                            let lit = (*clause)[k];
                            // Found a literal isn't false(true or undefined)
                            if self.vardata.eval(lit) != LitBool::False {
                                (*clause).swap(1, k);
                                ws.swap_remove(idx);

                                (*watchers_ptr)[!(*clause)[1]].push(w);
                                // NOTE
                                // Don't increase `idx` because you replace and the idx element with the last one.
                                continue 'next_clause;
                            }
                        }

                        //debug_assert_eq!(watcher[idx], cr);

                        if self.vardata.eval(first) == LitBool::False {
                            // CONFLICT
                            // a first literal(clause[0]) is false.
                            // clause[1] is a false
                            // clause[2..len] is a false
                            conflict = Some(cr);
                            break 'conflict;
                        } else {
                            // UNIT PROPAGATION
                            // a first literal(clause[0]) isn't assigned.
                            // clause[1] is a false
                            // clause[2..len] is a false
                            self.vardata.enqueue(first, Some(cr));
                        }
                    }
                    idx += 1;
                }
            }
            conflict
        }
        fn locked(&self, cref: CRef) -> bool {
            let c = self.db[cref][0];
            if self.vardata.eval(c) == LitBool::True {
                if let Some(reason) = self.vardata.reason[c.var()].as_ref() {
                    return *reason == cref;
                }
            }
            false
        }
        fn unwatch_clause(&mut self, cref: CRef) {
            let clause = &self.db[cref];
            let ws = &mut self.watchers[!clause[0]];
            ws.swap_remove(ws.iter().position(|&w| w.cref == cref).expect("Not found"));
            let ws = &mut self.watchers[!clause[1]];
            ws.swap_remove(ws.iter().position(|&w| w.cref == cref).expect("Not found"));
        }
        fn reduce_learnts(&mut self) {
            let mut learnts: Vec<_> = self
                .db
                .learnts
                .iter()
                .map(|&cr| (self.db[cr].activity(), self.db[cr].len(), cr))
                .collect();
            learnts.sort_by(|x, y| {
                Ord::cmp(&(x.1 <= 2), &(y.1 <= 2))
                    .then(PartialOrd::partial_cmp(&x.0, &y.0).expect("NaN activity"))
            });
            let n = learnts.len();

            let extra_lim = self.db.clause_inc / n as f32;
            debug_assert!(!extra_lim.is_nan());

            self.db.learnts.clear();

            for (i, (act, len, cr)) in learnts.into_iter().enumerate() {
                debug_assert!(!act.is_nan());
                if (i < n / 2 || act < extra_lim) && len > 2 && !self.locked(cr) {
                    self.detach_clause(cr);
                } else {
                    self.db.learnts.push(cr);
                }
            }

            self.db.collect_garbage_if_needed(
                &mut self.watchers,
                &mut self.vardata.reason,
                &mut self.vardata.trail.stack,
            );
        }

        fn pop_trail_until(&mut self, backtrack_level: usize) {
            if self.vardata.trail.decision_level() <= backtrack_level {
                return;
            }

            let trail = &mut self.vardata.trail;
            let sep = trail.stack_limit[backtrack_level];
            for p in trail.stack.iter().skip(sep).rev() {
                let x = p.var();
                if !self.order_heap.in_heap(x) {
                    self.order_heap.push(x);
                }
                self.vardata.polarity[x] = p.pos();
                self.vardata.assigns[x] = LitBool::Undef;
                self.vardata.reason[x] = None;
                self.vardata.level[x] = TOP_LEVEL;
            }
            trail.peek_head = sep;
            trail.stack.truncate(sep);
            trail.stack_limit.truncate(backtrack_level);
        }

        fn detach_if_satisfied(&mut self, cr: CRef) -> bool {
            let mut detach = false;
            for &lit in self.db[cr].iter() {
                if self.vardata.eval(lit) == LitBool::True {
                    self.detach_clause(cr);
                    detach = true;
                    break;
                }
            }
            detach
        }
        fn detach_clause(&mut self, cr: CRef) {
            // A "lit" is a asserting clause
            let lit = self.db[cr][0];
            self.unwatch_clause(cr);

            if self.locked(cr) {
                debug_assert!(self.vardata.reason[lit.var()].is_some());
                self.vardata.reason[lit.var()] = None;
            }
            self.db.free(cr);
        }

        fn simplify(&mut self) -> bool {
            debug_assert!(self.vardata.trail.decision_level() == TOP_LEVEL);

            if self.propagate().is_some() {
                return false;
            }
            if self.vardata.num_assings() as i32 == self.simplify_db.simp_db_assigns {
                return true;
            }

            {
                // learnts
                let n: usize = self.db.learnts.len();
                let mut new_size = 0;
                for i in 0..n {
                    let cr = self.db.learnts[i];
                    let detach = self.detach_if_satisfied(cr);
                    if !detach {
                        self.db.learnts[new_size] = cr;
                        new_size += 1;
                    }
                }
                self.db.learnts.truncate(new_size);
            }

            {
                // clauses
                let n: usize = self.db.clauses.len();
                let mut new_size = 0;
                for i in 0..n {
                    let cr = self.db.clauses[i];
                    let detach = self.detach_if_satisfied(cr);
                    if !detach {
                        self.db.clauses[new_size] = cr;
                        new_size += 1;
                    }
                }
                self.db.clauses.truncate(new_size);
            }

            self.db.collect_garbage_if_needed(
                &mut self.watchers,
                &mut self.vardata.reason,
                &mut self.vardata.trail.stack,
            );

            self.simplify_db.simp_db_assigns = self.vardata.num_assings() as i32;
            true
        }

        fn lit_redundant(&mut self, cr: CRef, abstract_levels: u32) -> bool {
            // Check whether a literal can reach a decision variable or unit clause literal.
            // Self-subsume
            let seen = &mut self.analyzer.seen;
            let ccmin_stack = &mut self.analyzer.ccmin_stack;
            let ccmin_clear = &mut self.analyzer.ccmin_clear;
            ccmin_stack.clear();
            ccmin_stack.push(cr);

            let top = ccmin_clear.len();
            let mut redundant = true;
            'redundant: while let Some(cr) = ccmin_stack.pop() {
                let clause = &self.db[cr];

                for c in clause.iter().skip(1) {
                    if !seen[c.var()] && self.vardata.level(c.var()) > TOP_LEVEL {
                        // If a 'c' is decided by a level that is different from conflict literals.
                        // abstract_level(c) & abstract_levels == 0
                        let intersect = Solver::abstract_level(self.vardata.level(c.var()))
                            & abstract_levels
                            != 0;
                        if !intersect {
                            redundant = false;
                            break 'redundant;
                        }

                        if let Some(cr) = self.vardata.reason[c.var()] {
                            seen[c.var()] = true;
                            ccmin_stack.push(cr);
                            ccmin_clear.push(*c);
                        } else {
                            redundant = false;
                            break 'redundant;
                        }
                    }
                }
            }
            if !redundant {
                // A 'c' is a decision variable or unit clause literal.
                // which means a "lit" isn't redundant
                for lit in ccmin_clear.iter().skip(top) {
                    seen[lit.var()] = false;
                }
                ccmin_clear.truncate(top);
            }
            redundant
        }

        fn abstract_level(level: usize) -> u32 {
            1 << (level as u32 & 31)
        }
        fn minimize_conflict_clause(&mut self) {
            debug_assert!(self.analyzer.ccmin_stack.is_empty());
            debug_assert!(self.analyzer.ccmin_clear.is_empty());

            let abstract_levels = self
                .analyzer
                .learnt_clause
                .iter()
                .skip(1)
                .fold(0, |als: u32, x| {
                    als | Solver::abstract_level(self.vardata.level(x.var()))
                });

            // Simplify conflict clauses
            let n: usize = self.analyzer.learnt_clause.len();
            let mut new_size = 1;
            for i in 1..n {
                let lit = self.analyzer.learnt_clause[i];

                let redundant = {
                    // Traverse a conflict literal to check wheter a literal is redundant.
                    if let Some(cr) = self.vardata.reason[lit.var()] {
                        self.lit_redundant(cr, abstract_levels)
                    } else {
                        false
                    }
                };

                if !redundant {
                    self.analyzer.learnt_clause[new_size] = lit;
                    new_size += 1;
                }
            }
            // clear all
            for lit in self.analyzer.ccmin_clear.iter() {
                self.analyzer.seen[lit.var()] = false;
            }
            self.analyzer.ccmin_stack.clear();
            self.analyzer.ccmin_clear.clear();
            self.analyzer.learnt_clause.truncate(new_size);
        }
        /// Analyze a conflict clause and deduce a learnt clause to avoid a current conflict
        fn analyze(&mut self, confl: CRef) {
            // seen must be clear
            debug_assert!(self.analyzer.seen.iter().all(|&x| !x));

            let decision_level = self.vardata.trail.decision_level();
            self.analyzer.learnt_clause.clear();

            let mut same_level_cnt = 0;

            if self.db[confl].learnt() {
                self.db.bump_activity(confl);
            }

            let clause = &self.db[confl];

            debug_assert!(!clause.free);
            // implication graph nodes that are start point from a conflict clause.
            for p in clause.iter() {
                let var = p.var();
                debug_assert!(self.vardata.eval(*p) != LitBool::Undef);

                self.order_heap.bump_activity(var);
                // already checked
                self.analyzer.seen[var] = true;

                //debug_assert!(self.vardata.level[var] <= decision_level);
                if self.vardata.level(var) < decision_level {
                    self.analyzer.learnt_clause.push(*p);
                } else {
                    same_level_cnt += 1;
                }
            }

            // Traverse an implication graph to 1-UIP(unique implication point)
            let first_uip = {
                let mut p = None;
                for &lit in self.vardata.trail.stack.iter().rev() {
                    let v = lit.var();

                    // Skip a variable that isn't checked.
                    if !self.analyzer.seen[v] {
                        continue;
                    }
                    self.analyzer.seen[v] = false;
                    self.order_heap.bump_activity(v);

                    debug_assert_eq!(self.vardata.level[v], decision_level);
                    same_level_cnt -= 1;
                    // There is no variables that are at the conflict level
                    if same_level_cnt <= 0 {
                        p = Some(lit);
                        break;
                    }

                    debug_assert!(self.vardata.reason[v].is_some());
                    let reason = self.vardata.reason[v].as_ref().expect("No reason");
                    if self.db[*reason].learnt() {
                        self.db.bump_activity(*reason);
                    }

                    let clause = &self.db[*reason];
                    for p in clause.iter().skip(1) {
                        let var = p.var();
                        // already checked
                        if self.analyzer.seen[var] {
                            continue;
                        }
                        self.analyzer.seen[var] = true;
                        debug_assert!(self.vardata.level(var) <= decision_level);
                        if self.vardata.level(var) < decision_level {
                            self.analyzer.learnt_clause.push(*p);
                        } else {
                            same_level_cnt += 1;
                        }
                    }
                }
                p
            };

            // p is 1-UIP.
            {
                let p = first_uip.expect("Not found first uip");
                self.analyzer.learnt_clause.push(!p);
                let n = self.analyzer.learnt_clause.len();
                self.analyzer.learnt_clause.swap(0, n - 1);
            }

            self.analyzer
                .analyze_toclear
                .clone_from(&self.analyzer.learnt_clause);
            self.minimize_conflict_clause();

            let backtrack_level = if self.analyzer.learnt_clause.len() == 1 {
                TOP_LEVEL
            } else {
                let mut max_idx = 1;
                let mut max_level = self
                    .vardata
                    .level(self.analyzer.learnt_clause[max_idx].var());
                for (i, lit) in self.analyzer.learnt_clause.iter().enumerate().skip(2) {
                    if self.vardata.level(lit.var()) > max_level {
                        max_level = self.vardata.level(lit.var());
                        max_idx = i;
                    }
                }

                self.analyzer.learnt_clause.swap(1, max_idx);
                max_level
            };

            // Cancel decisions until the level is less than equal to the backtrack level
            self.pop_trail_until(backtrack_level);

            // propagate it by a new learnt clause
            let first = self.analyzer.learnt_clause[0];
            if self.analyzer.learnt_clause.len() == 1 {
                debug_assert_eq!(backtrack_level, TOP_LEVEL);

                self.vardata.enqueue(first, None);
            } else {
                let cr = self.add_clause_db(&self.analyzer.learnt_clause.clone(), true);
                self.db.bump_activity(cr);
                self.vardata.enqueue(first, Some(cr));
            }

            // Clear seen
            for lit in self.analyzer.analyze_toclear.iter() {
                self.analyzer.seen[lit.var()] = false;
            }
        }
        fn define(&self, x: Var) -> bool {
            self.vardata.assigns[x] != LitBool::Undef
        }

        /// Reserve the space of a clause database
        /// # Arguments
        /// * `cla_num` - The number of clause
        pub fn reserve_clause(&mut self, cla_num: usize) {
            self.db.clauses.reserve(cla_num);
        }
        // Reserve the space of variables
        /// # Arguments
        /// * `var_num` - The number of variable
        pub fn reserve_variable(&mut self, var_num: usize) {
            self.vardata.trail.stack.reserve(var_num);
            self.db.clauses.reserve(var_num);
            self.vardata.reason.reserve(var_num);
            self.vardata.level.reserve(var_num);
            self.vardata.assigns.reserve(var_num);
        }

        fn search(&mut self, nof_conflicts: i32) -> Status {
            let mut conflict_cnt = 0;
            loop {
                if let Some(confl) = self.propagate() {
                    //Conflict
                    conflict_cnt += 1;
                    if self.vardata.trail.decision_level() == TOP_LEVEL {
                        self.status = Some(Status::Unsat);
                        return Status::Unsat;
                    }

                    self.analyze(confl);
                    self.order_heap.decay_inc();
                    self.db.decay_inc();

                    self.learnt_size_start.dec_adjust_cnt();
                    self.learnt_size_start.adjust_if_needed();
                } else {
                    // No Conflict
                    if conflict_cnt >= nof_conflicts {
                        self.pop_trail_until(TOP_LEVEL);
                        return Status::Indeterminate;
                    }

                    if self.vardata.trail.decision_level() == TOP_LEVEL && !self.simplify() {
                        return Status::Unsat;
                    }

                    if self.learnt_size_start.max_learnts + self.vardata.trail.stack.len() as f64
                        <= self.db.learnts.len() as f64
                    {
                        self.reduce_learnts();
                    }

                    // Select a decision variable that isn't decided yet
                    loop {
                        if let Some(v) = self.order_heap.pop() {
                            if self.define(v) {
                                continue;
                            }
                            let lit = Lit::new(v.0, self.vardata.polarity[v]);
                            self.vardata.trail.new_descion_level();
                            self.vardata.enqueue(lit, None);
                            break;
                        } else {
                            // all variables are selected. which means that a formula is satisfied
                            self.status = Some(Status::Sat);
                            self.models = self.vardata.assigns.clone();
                            return Status::Sat;
                        }
                    }
                }
            }
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
            // Initialization
            self.learnt_size_start.init(self.db.clauses.len());
            let mut status = Status::Indeterminate;
            let mut restart_cnt = 0;
            while status == Status::Indeterminate {
                if let Some(time_limit) = time_limit {
                    if start.elapsed() > time_limit {
                        // exceed the time limit
                        self.status = Some(Status::Indeterminate);
                        return Status::Indeterminate;
                    }
                }
                let nof_conflicts = self.restart_strat.luby(restart_cnt) as i32;
                status = self.search(nof_conflicts);
                restart_cnt += 1;
            }
            status
        }
    }
}

// This mod contains utility functions
pub mod util {
    use super::solver::Lit;
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
