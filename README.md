# screwsat
[![Crates.io](https://img.shields.io/crates/v/screwsat)](https://crates.io/crates/screwsat)

A very simple CDCL SAT Solver in `Rust`.  
This code is really inspired by [no522's SAT Solver](https://github.com/not522/CompetitiveProgramming/blob/master/include/math/sat.hpp).  

# How to use
`screwsat` can be used as a library and a command line tool. 

## As a cmd line tool
### Install
```
% cargo install --locked screwsat
```

### Usage
```
% screwsat --help
USAGE: screwsat [options] <input-file> [output-file]

% cat cnf/sat/sat.cnf
c Here is a comment.
c SATISFIABLE
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0

% screwsat cnf/sat/sat.cnf
s SATISFIABLE
-1 -2 -3 -4 -5 0

% screwsat cnf/unsat/unsat.cnf
s UNSATISFIABLE

% screwsat cnf/sat/sat.cnf sat_result.txt
% cat sat_result.txt
SAT
-1 -2 -3 -4 -5 0

```

## As a library
