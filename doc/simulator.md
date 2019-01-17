## Simulator Usage

The ProbReach simulator provides simulation of the provided *.pdrh* model and produces *.json* file as output.

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
make simulate
```

## Visualisation

The visulisation of the produced *.json* file is performed via a python script ```visualise.py``` 
located in ```probreach/src/python``` directory. This script requires [pandas](https://pandas.pydata.org/) package. 

### Usage

	python visualise.py <var 1> <var 2> ... <var n> <path/to/output/file.json>

If no variables are specified in the command line, then all variables are visualised.


