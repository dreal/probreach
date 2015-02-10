ProbReach
=========
ProbReach - software for calculating bounded probabilistic reachability in hybrid systems with random continuous initial parameters. The first version of the tool supporting **multiple** continuous and discrete random variables and continuous **nondeterministic** parameters is now released.

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
Run `./ProbReach <options> <model-file.pdrh>`:

```
options:

-e <double> - length of probability interval or maximum length of the box (default 0.001)
-d <double> - prescision used to call dReach (default 0.001)
-l <string> - full path to dReach binary (default dReach)
-k <int> - reachability depth (default 0)
```
