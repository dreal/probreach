# ProbReach Confidence Interval Estimation Tool

The qmc_verifier tool provides CI estimation for chosen *.pdrh* model by using eight CI evaluation methods as part of the statistical engine of the Probreach tool.

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
make qmc_verifier
```

## Usage

	qmc_verifier <options> <solver-options> <file.pdrh/file.drh>

options:
```
-h - displays help message
-t - specifies the reachability depth
–-qmc-acc - specifies the half-size of the confidence interval computed by chosen CI estimation method
–-qmc-conf - specifies the confidence value for chosen CI estimation method
–-CI - defines a CI estimation method (CLT - CLT, AC - Agresti- Coull, W - Wilson, L - Logit, ANC - Anscombe, ARC - Arcsine, Q - Qint, ALL - all listed methods)
–-verbose-result - provides detailed output
```