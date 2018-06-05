## Translator Usage

The translator from *.pdrh* to *Simulink®/Stateflow®* models is available as a separate tool alongside ProbReach.

## Requirements

 - The packages already listed under [How to Build](https://github.com/dreal/probreach/blob/master/doc/build.md)



 

 - And a local installation of MATLAB (version 2017b or later) with Simulink and Stateflow addons installed, as described [here](https://uk.mathworks.com/help/install/ug/install-mathworks-software.html).


## Configuration

 1. Having satisfied the requirements above, create a new environment variable MATLAB_ROOT and set it to the root directory of your MATLAB.

        export MATLAB_ROOT="/usr/local/MATLAB/R2018a/"

 ___


 2. Download the source code and compile it
	```
	git clone https://github.com/dreal/probreach.git probreach
	cd probreach
	mkdir -p build/release
	cd build/release
	cmake ../../
	```
	If you wish to compile only the translator
	```
	make pdrh2simulink
	```
	Otherwise,
	```
	make
	```
That completes the installation.
## Usage
To translate a given *.pdrh/.drh* to a Simulink model run
```
pdrh2simulink <path/to/model/file>
```
For example,
```
pdrh2simulink /home/user/repos/probreach/model/cars/collision.drh
```
Upon successful translation, an *.slx* file with a matching model name will be created in the directory of the executable pdrh2simulink. Note that since no valid Matlab identifiers can contain dashes in their name, all dashes, "-", in the input files are replaced with underscores "_".
