ProbReach
=========
ProbReach - application for calculating bounded probabilistic reachability in hybrid systems with random continuous initial parameters. Currently one continuous random variable is supported.

1. Required packages
--------------------
- [Boost.Regex](http://www.boost.org/doc/libs/1_55_0/libs/regex/doc/html/index.html) library
- [dReal/dReach](http://dreal.cs.cmu.edu/)
- [CAPD-4.0](http://capd.ii.uj.edu.pl/) library

2. Compilation
--------------------
- Edit Makefile:
 * `CAPDBINDIR = path/to/capd/bin`
 * `LDFLAGS = -lboost_regex -L/path/to/boost`

- Run `make` command in the `ProbReach` directory


3. Usage
--------------------
Run `./ProbReach <settings-file>` where the settings file should be of the following structure:

```
param:
<integral precision> - length of the interval containing the exact value of probability
model:
<model-file.pdrh> - bounded reachability encoded in pdrh format
<model-file-c.pdrh> - complement of bounded reachability encoded in pdrh format
dReach:
<depth of reachability analysis>
dReal:
<list of dReal options>
```