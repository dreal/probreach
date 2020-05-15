# ProbReach Gaussian Process GPEP tool

The GPEP tool performs Gaussian Process classification via Expectation Propagation algorithm for chosen *.pdrh* model.

## Required packages
    
   - [gcc/g++](https://gcc.gnu.org/) 4.9 or greater.
   - [GNU Bison](https://www.gnu.org/software/bison/) and [Flex](https://github.com/westes/flex)
      
        ```sudo apt-get install bison flex``` 
        
   - [CMake](https://cmake.org/), if not already present on your system.

## How to build

```
git clone https://github.com/dreal/probreach.git probreach
cd probreach
mkdir -p build/release
cd build/release
cmake ../../
make gp
```

## Usage

	gp <solver-options> <file.pdrh/file.drh> <options>

options:
```
-h - displays help message
-u - specifies the reachability depth
-n - specifies number of points (default = 20)
–-verbose - provides detailed output
–-conf - specifies the confidence of CIs for EP algorithm (default = 0.99)
–-samples - specifies number of samples (default = 20)
```
