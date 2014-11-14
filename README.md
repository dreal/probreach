ProbReach
=========
ProbReach - software for calculating bounded probabilistic reachability in hybrid systems with random continuous initial parameters. The first version of the tool supporting **multiple** random variables is now released.

1. Required packages
--------------------
- [gcc-4.9](https://gcc.gnu.org/gcc-4.9/) or [clang-3.5](http://clang.llvm.org/docs/ReleaseNotes.html)
- [dReal/dReach](https://github.com/dreal/dreal)
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
<precision> - length of the interval containing the exact value of probability
model:
<path/to/model/file.pdrh> - bounded reachability encoded in `pdrh` format
<path/to/model/file-c.pdrh> - negation of bounded reachability encoded in `pdrh` format
dReach:
<depth> - depth of reachability analysis>
```
