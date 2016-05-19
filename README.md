<a href="http://homepages.cs.ncl.ac.uk/f.shmarov/probreach/" target="_blank">
        <img style="align:center" src="http://homepages.cs.ncl.ac.uk/f.shmarov/probreach/img/banner-alt.gif" alt="ProbReach banner"/>
</a>

ProbReach - software for calculating bounded probabilistic reachability in hybrid systems with uncertainty in initial parameters.

*The parameter synthesis in hybrid systems is not currently supported.*

Install
====================
Latest version of static binary for Linux can be downloaded from ProbReach [releases page](https://github.com/dreal/probreach/releases)

How to Build
====================
1. Required packages
--------------------
In order to build ProbReach you will need to install the following packages
- [>=gcc-4.9](https://gcc.gnu.org/gcc-4.9/)
- [dReal](https://github.com/dreal/dreal3)
- [GSL](http://www.gnu.org/software/gsl/)

2. Build ProbReach
--------------------
```
git clone https://github.com/dreal/probreach.git probreach
cd probreach
mkdir -p build/release
cd build/release
cmake ../../
make
```
If your ```dReal``` location is different from ```/usr/local/src/dreal``` run
```
cmake -DDREAL_DIR=/path/to/dreal/directory ../../
```
