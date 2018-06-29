## Translator Usage

The translator from *.pdrh* to *Simulink®/Stateflow®* models is available as a separate tool alongside ProbReach.

## Requirements
    
   #### Required Packages
   
   - [gcc/g++](https://gcc.gnu.org/) 4.9 or greater. Ideally, consult the [MATLAB support page](https://uk.mathworks.com/support/compilers.html),
   and base your choice depending on the MATLAB version you are running, more on that [here](#matlab-version).
   
   - Only [GNU Bison](https://www.gnu.org/software/bison/) and [Flex](https://github.com/westes/flex)
   are required to build the translator. If you wish build the entire project, refer to 
   [these instructions](https://github.com/dreal/probreach/blob/master/doc/build.md).
   
        ```sudo apt-get install bison flex``` 
        
   - [CMake](https://cmake.org/), if not already present on your system.

 - Currently, the translator is only available for Linux, tested on Ubuntu 16.04, 17.10, 18.04 and Fedora 26

  #### MATLAB Version
 - Local installation of MATLAB (version 2017b or later) with Simulink and Stateflow add-ons installed, 
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
	Otherwise, assuming all packages required by ProbReach are installed.
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

#### Model decomposition
The translator provides the option to translate model plant and controller as separate Simulink subsystems. 
This mode of operation is enabled by providing the `--decompose` flag preceding the model file path. 


Having two distinct subsystems allows the user to create a processor-in-the-loop block (using MATLAB Simulink Coder)
of the controller and subsequently execute that on hardware of choice.

However, it should be noted that this mode of operation is not as precise in comparison to the regular
translation method and the Simulink states formalism used. This difference is owed to the creation of dummy states
used to resolve the loops found in .(p)drh by transitions to the same state.

---

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
