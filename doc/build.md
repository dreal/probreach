## Required packages

In order to build **ProbReach** you will need to install the following packages
- [>=gcc-4.9](https://gcc.gnu.org/gcc-4.9/)
- [dReal](https://github.com/dreal/dreal3)
- [GSL](http://www.gnu.org/software/gsl/)

## Build ProbReach
```
git clone https://github.com/dreal/probreach.git probreach
cd probreach
mkdir -p build/release
cd build/release
cmake ../../
make
```
If your **dReal** location is different from ```/usr/local/src/dreal``` run
```
cmake -DDREAL_DIR=/path/to/dreal/directory ../../
```
