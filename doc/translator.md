## Translator Usage

The translator from *.pdrh* to *Simulink®/Stateflow®* models is available as a separate tool alongside ProbReach.

## Requirements

 - The packages already listed under [How to Build](https://github.com/dreal/probreach/blob/master/doc/build.md)



 

 - And a local installation of MATLAB (version 2017b or later) with Simulink and Stateflow addons installed, 
 as described [here](https://uk.mathworks.com/help/install/ug/install-mathworks-software.html).


## Configuration

 1. Having satisfied the requirements above, create a new environment variable MATLAB_ROOT and set it to the root 
 directory of your MATLAB.

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
To translate a given *.pdrh/.drh* model to Simulink run
```
pdrh2simulink <path/to/model/file>
```
For example,
```
pdrh2simulink /home/user/repos/probreach/model/cars/collision.drh
```
An optional ```--verbose``` flag can be passed to the command line tool to print additional translation details.

Upon successful translation, a *.slx* file with a matching model name will be created
in the current directory. Note that since no valid Matlab 
identifiers can contain dashes in their name, all dashes, "-", in the input files are replaced with underscores "_".

## Model Advice

Some considerations need to be taken into account when developing models which are intended to be translated.

Expressing strong equality ```x = y``` in jump guards is discouraged as the 
translated Stateflow model might miss events (due to round-off errors, etc.) and the 
respective jump will not occur. Instead, encode these as inequalities - ```>=``` or ```<=``` - for increasing and 
decreasing values respectively. See the example below.
The translator cannot make any assumptions during execution about which inequality is to be used, leaving that 
responsibility to the user at this stage
until the option to specify tolerance values for the translated comparisons is implemented.

```
((v1 = 0))==>@4(and (s1' = s1) (s2' = s2) (v1' = v1) (v2' = v2) (v01' = v1) (v02' = v2) (tau' = 0));
```
For a decreasing value of ```v1``` in the active mode the expression should become
```
((v1 <= 0))==>@4(and (s1' = s1) (s2' = s2) (v1' = v1) (v2' = v2) (v01' = v1) (v02' = v2) (tau' = 0));
```
