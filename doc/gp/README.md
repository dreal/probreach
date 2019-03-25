# ProbReach Gaussian Process

<!--
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

## Usage

	simulate <options> <file.pdrh/file.drh>

options:
```
-h - displays help message
-v - displays the tool version
-l - minimum depth of every simulation path (default = 0)
-u - maximum depth of every simulation path (default = 0)
-p - maximum number of simulation paths (default = 1)
-n - number of points used in IVP solving (default = 1)
-o - full path to the output file (default = output.json)
-v - prints out the current version of ProbReach
```


# Visualisation

The visulisation of the produced *.json* file is performed via a python script ```visualise.py``` 
located in ```probreach/src/python``` directory. This script requires [pandas](https://pandas.pydata.org/) package. 

## Usage

	python visualise.py <var 1> <var 2> ... <var n> <path/to/output/file.json>

If no variables are specified in the command line, then all variables are visualised.

# Usage example

```
./simulate -u 300 -n 10 -o output.json ~/probreach/model/insulin-infusion/discrete-pid.pdrh
python ~/probreach/src/python/visualise.py Q1 u C output.json 
```
The commands above produce the following output:

![traj1](img/ex1.png)
![traj2](img/ex2.png)
-->
