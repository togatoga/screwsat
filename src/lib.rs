pub mod solver {

    use std::{
        fmt,
        marker::PhantomData,
        ops::{Index, IndexMut},
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

    struct ClauseRef<'a> {
        header: ClauseHeader,
        clause: &'a [ClauseData],
        extra: Option<ClauseData>,
    }

    impl<'a> ClauseRef<'a> {
        fn activity(&self) -> f32 {
            unsafe { self.extra.as_ref().expect("No activity").act }
        }
        fn len(&self) -> usize {
            self.clause.len()
        }
        #[allow(dead_code)]
        fn iter(&self) -> ClauseIter {
            ClauseIter(self.clause.iter())
        }
        pub fn reloced(&self) -> bool {
            self.header.reloced()
        }
        #[allow(dead_code)]
        pub fn relocation(&self) -> CRef {
            debug_assert!(self.reloced());
            unsafe { self.clause[0].cref }
        }
    }

    impl<'a> Index<usize> for ClauseRef<'a> {
        type Output = Lit;
        fn index(&self, idx: usize) -> &Self::Output {
            unsafe { &self.clause[idx].lit }
        }
    }

    struct ClauseMut<'a> {
        header: &'a mut ClauseHeader,
        clause: &'a mut [ClauseData],
        extra: Option<&'a mut ClauseData>,
    }

    impl<'a> ClauseMut<'a> {
        fn set_activity(&mut self, act: f32) {
            self.extra.as_mut().expect("No extra field").act = act;
        }
        fn activity(&self) -> f32 {
            unsafe { self.extra.as_ref().expect("No activity").act }
        }
        fn len(&self) -> usize {
            self.clause.len()
        }
        fn swap(&mut self, x: usize, y: usize) {
            self.clause.swap(x, y);
        }
        #[allow(dead_code)]
        fn iter(&self) -> ClauseIter {
            ClauseIter(self.clause.iter())
        }
        #[allow(dead_code)]
        fn iter_mut(&mut self) -> ClauseIterMut {
            ClauseIterMut(self.clause.iter_mut())
        }
        pub fn reloced(&self) -> bool {
            self.header.reloced()
        }
        pub fn relocation(&self) -> CRef {
            debug_assert!(self.reloced());
            unsafe { self.clause[0].cref }
        }
        pub fn set_reloced(&mut self, reloced: bool) {
            self.header.set_reloced(reloced);
        }
        pub fn relocate(mut self, c: CRef) {
            debug_assert!(!self.reloced());
            self.set_reloced(true);
            self.clause[0].cref = c;
        }

        pub fn as_clause_ref(&mut self) -> ClauseRef {
            ClauseRef {
                header: *self.header,
                clause: self.clause,
                extra: self.extra.as_mut().map(|extra| **extra),
            }
        }
    }

    impl<'a> Index<usize> for ClauseMut<'a> {
        type Output = Lit;
        fn index(&self, idx: usize) -> &Self::Output {
            unsafe { &self.clause[idx].lit }
        }
    }

    impl<'a> IndexMut<usize> for ClauseMut<'a> {
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            unsafe { &mut self.clause[index as usize].lit }
        }
    }

    #[derive(Debug, Clone)]
    pub struct ClauseIter<'a>(std::slice::Iter<'a, ClauseData>);

    impl<'a> Iterator for ClauseIter<'a> {
        type Item = &'a Lit;
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|lit| unsafe { &lit.lit })
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }
    impl<'a> DoubleEndedIterator for ClauseIter<'a> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.0.next_back().map(|lit| unsafe { &lit.lit })
        }
    }

    #[derive(Debug)]
    pub struct ClauseIterMut<'a>(std::slice::IterMut<'a, ClauseData>);

    impl<'a> Iterator for ClauseIterMut<'a> {
        type Item = &'a mut Lit;
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|lit| unsafe { &mut lit.lit })
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }
    impl<'a> DoubleEndedIterator for ClauseIterMut<'a> {
        fn next_back(&mut self) -> Option<Self::Item> {
            self.0.next_back().map(|lit| unsafe { &mut lit.lit })
        }
    }

    // Clause //

    #[derive(Debug)]
    struct RegionAllocator<T: Copy + Default> {
        data: Vec<T>,
        wasted: usize,
    }

    #[derive(Debug, Default, Clone, Copy)]
    struct Ref<T: Copy>(usize, PhantomData<T>);
    impl<T: Copy> PartialEq for Ref<T> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl<T: Copy> std::ops::Add<usize> for Ref<T> {
        type Output = Ref<T>;
        fn add(self, rhs: usize) -> Self::Output {
            Ref(self.0 + rhs, PhantomData)
        }
    }

    impl<T: Copy + Default> RegionAllocator<T> {
        fn new() -> RegionAllocator<T> {
            RegionAllocator {
                data: Vec::with_capacity(1024 * 1024),
                wasted: 0,
            }
        }
        fn with_capacity(n: usize) -> RegionAllocator<T> {
            RegionAllocator {
                data: Vec::with_capacity(n),
                wasted: 0,
            }
        }
        fn len(&self) -> usize {
            self.data.len()
        }
        fn capacity(&self) -> usize {
            self.data.capacity()
        }
        fn free(&mut self, size: usize) {
            debug_assert!(size <= self.capacity());
            self.wasted += size;
        }

        fn wasted(&self) -> usize {
            self.wasted
        }

        fn alloc(&mut self, size: usize) -> Ref<T> {
            let r = self.len();
            self.data.extend((0..size).map(|_| T::default()));

            Ref(r, PhantomData)
        }

        pub fn subslice(&self, r: Ref<T>, len: usize) -> &[T] {
            debug_assert!(len <= self.len());
            &self.data[r.0..r.0 + len]
        }
        pub fn subslice_mut(&mut self, r: Ref<T>, len: usize) -> &mut [T] {
            debug_assert!(len <= self.len());
            &mut self.data[r.0..r.0 + len]
        }
    }

    impl<T: Copy + Default> Index<Ref<T>> for RegionAllocator<T> {
        type Output = T;
        fn index(&self, r: Ref<T>) -> &Self::Output {
            &self.data[r.0]
        }
    }
    impl<T: Copy + Default> IndexMut<Ref<T>> for RegionAllocator<T> {
        fn index_mut(&mut self, r: Ref<T>) -> &mut Self::Output {
            &mut self.data[r.0]
        }
    }

    #[derive(Clone, Copy)]
    union ClauseData {
        lit: Lit,
        abs: u32,
        act: f32,
        header: ClauseHeader,
        cref: CRef,
    }

    impl Default for ClauseData {
        fn default() -> Self {
            ClauseData { abs: 0 }
        }
    }

    impl fmt::Debug for ClauseData {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("ClauseData")
                .field("abs", unsafe { &self.abs })
                .finish()
        }
    }
    // unsigned mark      : 2;
    // unsigned learnt    : 1;
    // unsigned has_extra : 1;
    // unsigned reloced   : 1;
    // unsigned size      : 27;
    #[derive(Clone, Copy)]
    pub struct ClauseHeader(u32);

    impl ClauseHeader {
        pub fn new(mark: u32, learnt: bool, has_extra: bool, reloced: bool, size: u32) -> Self {
            debug_assert!(mark < 4);
            debug_assert!(size < (1 << 27));
            ClauseHeader(
                (mark << 30)
                    | ((learnt as u32) << 29)
                    | ((has_extra as u32) << 28)
                    | ((reloced as u32) << 27)
                    | size,
            )
        }
        pub fn mark(&self) -> u32 {
            self.0 >> 30
        }
        pub fn free(&self) -> bool {
            self.mark() == 1
        }
        pub fn learnt(&self) -> bool {
            (self.0 & (1 << 29)) != 0
        }
        pub fn has_extra(&self) -> bool {
            (self.0 & (1 << 28)) != 0
        }
        pub fn reloced(&self) -> bool {
            (self.0 & (1 << 27)) != 0
        }
        pub fn size(&self) -> u32 {
            self.0 & ((1 << 27) - 1)
        }
        pub fn set_mark(&mut self, mark: u32) {
            debug_assert!(mark < 4);
            self.0 = (self.0 & !(3 << 30)) | (mark << 30);
        }
        pub fn set_learnt(&mut self, learnt: bool) {
            self.0 = (self.0 & !(1 << 29)) | ((learnt as u32) << 29);
        }
        pub fn set_has_extra(&mut self, has_extra: bool) {
            self.0 = (self.0 & !(1 << 28)) | ((has_extra as u32) << 28);
        }
        pub fn set_reloced(&mut self, reloced: bool) {
            self.0 = (self.0 & !(1 << 27)) | ((reloced as u32) << 27);
        }
        pub fn set_size(&mut self, size: u32) {
            debug_assert!(size < (1 << 27));
            self.0 = (self.0 & !((1 << 27) - 1)) | size;
        }
    }

    type CRef = Ref<ClauseData>;

    #[derive(Debug)]
    struct ClauseAllocator {
        ra: RegionAllocator<ClauseData>,
    }

    impl ClauseAllocator {
        fn new() -> ClauseAllocator {
            ClauseAllocator {
                ra: RegionAllocator::new(),
            }
        }
        fn with_capacity(n: usize) -> ClauseAllocator {
            ClauseAllocator {
                ra: RegionAllocator::with_capacity(n),
            }
        }

        fn unit_region(len: usize, extra: bool) -> usize {
            //header + clause + other
            1 + len + extra as usize
        }
        fn alloc(&mut self, clause: &[Lit], learnt: bool) -> CRef {
            let use_extra = learnt;
            let cid = self
                .ra
                .alloc(ClauseAllocator::unit_region(clause.len(), learnt));
            self.ra[cid].header =
                ClauseHeader::new(0, learnt, use_extra, false, clause.len() as u32);
            let clause_ptr = cid + 1;
            for (i, &lit) in clause.iter().enumerate() {
                self.ra[clause_ptr + i as usize].lit = lit;
            }

            if learnt {
                self.ra[clause_ptr + clause.len() as usize].act = 0.0;
            }

            cid
        }

        pub fn alloc_copy(&mut self, from: ClauseRef) -> CRef {
            let use_extra = from.header.learnt();
            let cid = self
                .ra
                .alloc(1 + from.header.size() as usize + use_extra as usize);
            self.ra[cid].header = from.header;
            // NOTE: the copied clause may lose the extra field.
            unsafe { &mut self.ra[cid].header }.set_has_extra(use_extra);
            for (i, &lit) in from.iter().enumerate() {
                self.ra[cid + 1 + i as usize].lit = lit;
            }
            if use_extra {
                self.ra[cid + 1 + from.len() as usize] = from.extra.expect("Extra");
            }
            cid
        }

        pub fn free(&mut self, cr: CRef) {
            let size = {
                let c = self.get(cr);
                1 + c.len() + c.header.has_extra() as usize
            };
            self.ra.free(size);
        }

        pub fn reloc(&mut self, cr: &mut CRef, to: &mut ClauseAllocator) {
            let mut c = self.get_mut(*cr);

            if c.header.reloced() {
                *cr = c.relocation();
                return;
            }

            *cr = to.alloc_copy(c.as_clause_ref());
            c.relocate(*cr);
        }

        fn get(&self, cref: CRef) -> ClauseRef {
            let header = unsafe { self.ra[cref].header };
            let has_extra = header.has_extra();
            let size = header.size();

            let clause = self.ra.subslice(cref + 1, size as usize);
            let extra = if has_extra {
                Some(self.ra[cref + 1 + size as usize])
            } else {
                None
            };
            ClauseRef {
                header,
                clause,
                extra,
            }
        }
        fn get_mut(&mut self, cref: CRef) -> ClauseMut {
            let header = unsafe { self.ra[cref].header };
            let has_extra = header.has_extra();
            let size = header.size();
            let len = 1 + size + has_extra as u32;

            let subslice = self.ra.subslice_mut(cref, len as usize);
            let (subslice0, subslice) = subslice.split_at_mut(1);
            let (subslice1, subslice2) = subslice.split_at_mut(size as usize);
            ClauseMut {
                header: unsafe { &mut subslice0[0].header },
                clause: subslice1,
                extra: subslice2.first_mut(),
            }
        }

        fn len(&self) -> usize {
            self.ra.len()
        }
        fn wasted(&self) -> usize {
            self.ra.wasted()
        }
    }

    // Clause //

    #[derive(Debug)]
    struct ClauseDB {
        // original
        clauses: Vec<CRef>,
        // learnts
        learnts: Vec<CRef>,
        db: ClauseAllocator,
        clause_inc: f32,
    }

    impl Default for ClauseDB {
        fn default() -> Self {
            let mut clause = ClauseDB::new();
            clause.clause_inc = 1.0;
            clause
        }
    }

    impl ClauseDB {
        pub fn new() -> ClauseDB {
            ClauseDB {
                clauses: Vec::new(),
                learnts: Vec::new(),
                clause_inc: 0.0,
                db: ClauseAllocator::new(),
            }
        }

        fn bump_activity(&mut self, cr: CRef) {
            let act = {
                let mut clause = self.db.get_mut(cr);
                //debug_assert!(self[cr].learnt());
                //debug_assert!(self.clause_inc >= 0.0);
                let new_act = clause.activity() + self.clause_inc as f32;
                clause.set_activity(new_act);
                new_act
            };

            if act > 1e20 {
                // Rescale
                let n: usize = self.learnts.len();
                for i in 0..n {
                    let x = self.learnts[i];
                    let mut clause = self.db.get_mut(x);
                    debug_assert!(clause.header.learnt());
                    let new_act = clause.activity() * 1e-20;
                    clause.set_activity(new_act);
                }

                self.clause_inc *= 1e-20;
            }
        }

        fn decay_inc(&mut self) {
            self.clause_inc *= 1.0 / 0.999;
        }

        pub fn push(&mut self, lits: &[Lit], learnt: bool) -> CRef {
            let cref = self.db.alloc(lits, learnt);
            if learnt {
                self.learnts.push(cref);
            } else {
                self.clauses.push(cref);
            }
            cref
        }

        fn need_collect_garbage(&mut self) -> bool {
            self.db.wasted() * 10 > self.db.len() * 2
        }

        fn collect_garbage_if_needed(
            &mut self,
            watchers: &mut Vec<Vec<Watcher>>,
            vardata: &mut VarData,
        ) {
            if self.need_collect_garbage() {
                self.collect_garbage(watchers, vardata);
            }
        }
        fn collect_garbage(&mut self, watchers: &mut Vec<Vec<Watcher>>, vardata: &mut VarData) {
            let mut to = ClauseAllocator::with_capacity(self.db.len() - self.db.wasted());

            for watcher in watchers.iter_mut() {
                for ws in watcher.iter_mut() {
                    self.db.reloc(&mut ws.cref, &mut to);
                }
            }

            // All reasons:
            {
                let trail = &vardata.trail.stack;
                for &lit in trail.iter() {
                    let cond = if let Some(cref) = vardata.reason[lit.var()] {
                        let c = self.db.get(cref);
                        c.reloced() || vardata.locked(c[0], cref)
                    } else {
                        false
                    };
                    if cond {
                        let mut cref = vardata.reason[lit.var()].as_mut().expect("not found");
                        self.db.reloc(&mut cref, &mut to);
                    }
                }
            }

            // All learnts
            {
                let mut j = 0;
                for i in 0..self.learnts.len() {
                    let mut cr = self.learnts[i];
                    let removed = self.db.get(cr).header.free();
                    if !removed {
                        self.db.reloc(&mut cr, &mut to);
                        self.learnts[j] = cr;
                        j += 1;
                    }
                }
                self.learnts.truncate(j);
            }

            // All orignal:
            {
                let mut j = 0;
                for i in 0..self.clauses.len() {
                    let mut cr = self.clauses[i];
                    let removed = self.db.get(cr).header.free();
                    if !removed {
                        self.db.reloc(&mut cr, &mut to);
                        self.clauses[j] = cr;
                        j += 1;
                    }
                }

                self.clauses.truncate(j);
            }

            self.db = to;
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
        fn locked(&self, c: Lit, cref: CRef) -> bool {
            if self.eval(c) == LitBool::True {
                if let Some(reason) = self.reason[c.var()].as_ref() {
                    return *reason == cref;
                }
            }
            false
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
                    
                    if self.vardata.eval(blocker) == LitBool::True {
                        idx += 1;
                        continue;
                    }
                    
                    let cr = ws[idx].cref;
                    let mut clause = self.db.db.get_mut(cr);

                    debug_assert!(!clause.header.free());
                    debug_assert!(clause[0] == !p || clause[1] == !p);

                    // make sure that the clause[1] is the false literal.
                    if clause[0] == !p {
                        clause.swap(0, 1);
                    }
                    let first = clause[0];
                    let w = Watcher::new(cr, first);
                    // already satisfied
                    if first != blocker && self.vardata.eval(first) == LitBool::True {
                        debug_assert!(first != clause[1]);
                        ws[idx] = w;
                        idx += 1;
                        continue 'next_clause;
                    }

                    for k in 2..clause.len() {
                        let lit = clause[k];
                        // Found a literal isn't false(true or undefined)
                        if self.vardata.eval(lit) != LitBool::False {
                            clause.swap(1, k);
                            ws.swap_remove(idx);

                            unsafe { &mut (*watchers_ptr)[!clause[1]].push(w) };
                            // NOTE
                            // Don't increase `idx` because you replace and the idx element with the last one.
                            continue 'next_clause;
                        }
                    }
                    ws[idx] = w;
                    if self.vardata.eval(first) == LitBool::False {
                        // CONFLICT
                        // a first literal(clause[0]) is false.
                        // clause[1] is a false
                        // clause[2..len] is a false
                        self.vardata.trail.peek_head = self.vardata.trail.stack.len();
                        conflict = Some(cr);
                        break 'conflict;
                    } else {
                        // UNIT PROPAGATION
                        // a first literal(clause[0]) isn't assigned.
                        // clause[1] is a false
                        // clause[2..len] is a false
                        self.vardata.enqueue(first, Some(cr));
                    }

                    idx += 1;
                }
            }
            conflict
        }

        fn unwatch_clause(&mut self, cref: CRef) {
            let clause = self.db.db.get(cref);
            let ws = &mut self.watchers[!clause[0]];
            ws.swap_remove(ws.iter().position(|&w| w.cref == cref).expect("Not found"));
            let ws = &mut self.watchers[!clause[1]];
            ws.swap_remove(ws.iter().position(|&w| w.cref == cref).expect("Not found"));
        }
        fn reduce_learnts(&mut self) {
            let extra_lim = self.db.clause_inc / self.db.learnts.len() as f32;
            debug_assert!(!extra_lim.is_nan());
            {
                let ca = &self.db.db;
                self.db.learnts.sort_unstable_by(|&x, &y| {
                    let x = ca.get(x);
                    let y = ca.get(y);

                    Ord::cmp(&(x.len() <= 2), &(y.len() <= 2)).then(
                        PartialOrd::partial_cmp(&x.activity(), &y.activity())
                            .expect("NaN activity"),
                    )
                });
            }

            let mut new_size = 0;
            for i in 0..self.db.learnts.len() {
                let cr = self.db.learnts[i];
                let cla = self.db.db.get(cr);
                let act = cla.activity();
                let len = cla.len();

                if (i < self.db.learnts.len() / 2 || act < extra_lim)
                    && len > 2
                    && !self.vardata.locked(cla[0], cr)
                {
                    self.detach_clause(cr);
                } else {
                    self.db.learnts[new_size] = cr;
                    new_size += 1;
                }
            }

            //eprintln!("{} {}", new_size, self.db.learnts.len());
            self.db.learnts.truncate(new_size);

            self.db
                .collect_garbage_if_needed(&mut self.watchers, &mut self.vardata);
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
            let clause = self.db.db.get(cr);
            for &lit in clause.iter() {
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
            let lit = self.db.db.get(cr)[0];
            self.unwatch_clause(cr);

            if self.vardata.locked(lit, cr) {
                debug_assert!(self.vardata.reason[lit.var()].is_some());
                self.vardata.reason[lit.var()] = None;
            }
            self.db.db.get_mut(cr).header.set_mark(1);

            self.db.db.free(cr);
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

            self.db
                .collect_garbage_if_needed(&mut self.watchers, &mut self.vardata);

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
                let clause = self.db.db.get(cr);

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
            self.analyzer.learnt_clause.push(Lit::default());

            let mut same_level_cnt = 0;

            {
                let learnt = self.db.db.get(confl).header.learnt();

                if learnt {
                    self.db.bump_activity(confl);
                }

                let clause = self.db.db.get(confl);
                debug_assert!(!clause.header.free());
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

                    debug_assert_eq!(self.vardata.level[v], decision_level);
                    same_level_cnt -= 1;
                    // There is no variables that are at the conflict level
                    if same_level_cnt <= 0 {
                        p = Some(lit);
                        break;
                    }

                    debug_assert!(self.vardata.reason[v].is_some());
                    let reason = self.vardata.reason[v].as_ref().expect("No reason");
                    let learnt = self.db.db.get(*reason).header.learnt();

                    if learnt {
                        self.db.bump_activity(*reason);
                    }
                    let clause = self.db.db.get(*reason);

                    for p in clause.iter().skip(1) {
                        let var = p.var();
                        // already checked
                        if self.analyzer.seen[var] {
                            continue;
                        }
                        self.order_heap.bump_activity(var);
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
            self.analyzer.learnt_clause[0] = !first_uip.expect("not found first uip");

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
