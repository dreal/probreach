<a href="http://homepages.cs.ncl.ac.uk/f.shmarov/probreach/" target="_blank">
        <img style="align:center" src="http://homepages.cs.ncl.ac.uk/f.shmarov/probreach/img/banner-alt.gif" alt="ProbReach banner"/>
</a>

ProbReach - software for calculating bounded probabilistic reachability in hybrid systems with uncertainty in initial parameters. The first version of the tool supporting **multiple** continuous and discrete random variables and continuous **nondeterministic** parameters is now released.

Download
====================
Latest version of static binary for Linux can be downloaded from ProbReach [releases page](https://github.com/dreal/probreach/releases)

How to Build
====================

1. Required packages
--------------------
- [gcc-4.9](https://gcc.gnu.org/gcc-4.9/)
- [dReal/dReach](https://github.com/dreal/dreal)
- [ibex](http://www.ibex-lib.org/)
- [capd-4.0](http://capd.ii.uj.edu.pl/)


2. Compilation (with gcc-4.9 or later)
--------------------

###2.1. Default compilation
```
cd probreach/src
make CXX=g++-4.9 CC=gcc-4.9 CAPDBINDIR=/path/to/capd-4/bin/
make install
```
###2.2. Compiling with [OpenMP](www.openmp.org/)
```
cd probreach/src
make CXX=g++-4.9 CC=gcc-4.9 CAPDBINDIR=/path/to/capd-4/bin/ WITHOMP=yes
make install
```
The executables can be accessed at `probreach/bin`

3. Usage
--------------------
Run ```./ProbReach <options> <model-file.pdrh> --dreach <dReach-options> --dreal <dReal-options>```

```
options:
        -e <double> - length of probability interval or maximum length of the box (default 0.001)
        -l <string> - full path to dReach binary (default dReach)
        -t <int> - number of CPU cores (default 1)
        -h/--help - help message
        --version - version of the tool
        --verbose - output computation details
        --visualize <string> - produces <model-file.json> containing Borel set for parameter <string> and probability value with respect to time
        --dreach - delimits dReach options (e.g. rechability depth)
        --dreal - delimits dReal options (e.g. precision, ode step)
```

Current version of ```ProbReach``` computes exactly ```-k``` step probability reachability. Using ```dReach``` version supporting up to ```-k``` steps reachability (with```-l``` and ```-u``` flags) ```-l``` must be specified and be equal to ```-k```.
