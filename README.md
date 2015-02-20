ProbReach
=========
ProbReach - software for calculating bounded probabilistic reachability in hybrid systems with uncertainty in initial parameters. The first version of the tool supporting **multiple** continuous and discrete random variables and continuous **nondeterministic** parameters is now released.

Download
====================
Latest version of static binary for Linux can be downloaded from ProbReach [releases page](https://github.com/dreal/probreach/releases)

How to Build
====================

1. Required packages
--------------------
- [gcc-4.9](https://gcc.gnu.org/gcc-4.9/) or [clang-3.5](http://clang.llvm.org/docs/ReleaseNotes.html)
- [dReal/dReach](https://github.com/dreal/dreal)
- [CAPD-4.0](http://capd.ii.uj.edu.pl/)

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
Run ```./ProbReach <options> <model-file.pdrh> <dReach-options>```

```
options:
        -e <double> - length of probability interval or maximum length of the box (default 0.001)
        -d <double> - prescision used to call dReach (default 0.001)
        -l <string> - full path to dReach binary (default dReach)
        -t <int> - number of CPU cores (default 1)
        -k <int> - reachability depth (default 0)
        -h/--help - help message
        --version - version of the tool
        --verbose - output computation details
```

Current version of ```ProbReach``` computes exactly ```-k``` step probability reachability. Using ```dReach``` version supporting up to ```-k``` steps reachability (with```-l``` and ```-u``` flags) ```-l``` must be specified and be equal to ```-k```.
