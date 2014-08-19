ProbReach
=========
ProbReach - application for calculating bounded probabilistic reachability in hybrid systems with random continuous initial parameters.

1. Required packages
=========
- [Boost.Regex](http://www.boost.org/doc/libs/1_55_0/libs/regex/doc/html/index.html) library

- [dReal/dReach](http://dreal.cs.cmu.edu/)

- [CAPD](http://capd.ii.uj.edu.pl/) library

2. Compilation
=========

- Edit Makefile:
--* CAPDBINDIR = path/to/capd/bin
--* LDFLAGS = -lboost_regex -L/path/to/boost
- Run `make` command in the `ProbReach` directory


3. Usage
=========

- run `./ProbReach <settings-file>` where the settings file should be of the following structure:
`param:
<integral precision>
model:
<model-file.pdrh> - 
<model-file-c.pdrh> - 
dReach:
<depth of reachability analysis>
dReal:
<list of options passed to the dReal>`