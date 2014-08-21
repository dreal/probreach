ProbReach
=========
ProbReach - software for calculating bounded probabilistic reachability in hybrid systems with random continuous initial parameters. Currently one continuous random variable is supported.

1. Required packages
--------------------
- [gcc-4.9](https://gcc.gnu.org/gcc-4.9/) or [clang-3.5](http://clang.llvm.org/docs/ReleaseNotes.html)
- [dReal/dReach](http://dreal.cs.cmu.edu/)
- [CAPD-4.0](http://capd.ii.uj.edu.pl/) library

2. Compilation
--------------------
- Edit Makefile:
 * `CAPDBINDIR = path/to/capd/bin`

```
cd ProbReach/src
make
make install
```

The executables can be accessed at `ProbReach/bin`

3. Usage
--------------------
Run `./ProbReach <settings-file>` where the settings file should be structured as following:

```
param:
<integral precision> - length of the interval containing the exact value of probability
model:
<model-file.pdrh> - bounded reachability encoded in `pdrh` format
<model-file-c.pdrh> - negation of bounded reachability encoded in `pdrh` format
dReach:
<depth of reachability analysis>
```