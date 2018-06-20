# - this module looks for Matlab
# Defines:
#  MATLAB_INCLUDE_DIR: include path for mex.h
#  MATLAB_LIBRARIES:   required libraries: libmex, libmx
#  MATLAB_MEX_LIBRARY: path to libmex
#  MATLAB_MX_LIBRARY:  path to libmx

SET(MATLAB_FOUND 0)
IF( "$ENV{MATLAB_ROOT}" STREQUAL "" )
    MESSAGE(STATUS " " )
    MESSAGE(STATUS " " )
    MESSAGE(STATUS " " )
    MESSAGE(STATUS " MATLAB not found. If you wish to use the translator utility, make sure MATLAB is installed and configured on the system." )
    MESSAGE(STATUS " On Linux, append the following to your .bashrc file or set it for the current session:" )
    MESSAGE(STATUS " >>> export MATLAB_ROOT=/usr/local/MATLAB/R2018a <<<" )
    MESSAGE(STATUS " be sure to pick the correct version of Matlab if you have one installed." )
    MESSAGE(STATUS " " )
    MESSAGE(STATUS " " )
    MESSAGE(STATUS " " )
#    MESSAGE(FATAL_ERROR " No matlab found. Follow the instructions above." )
ELSE("$ENV{MATLAB_ROOT}" STREQUAL "" )

        FIND_PATH(MATLAB_INCLUDE_DIR mex.h
                  $ENV{MATLAB_ROOT}/extern/include)

        INCLUDE_DIRECTORIES(${MATLAB_INCLUDE_DIR})

#        FIND_LIBRARY( MATLAB_MEX_LIBRARY
#                      NAMES libmex mex
#                      PATHS $ENV{MATLAB_ROOT}/bin $ENV{MATLAB_ROOT}/extern/lib
#                      PATH_SUFFIXES glnxa64 glnx86)
#
#        FIND_LIBRARY( MATLAB_ENG_LIBRARY
#                      NAMES libeng eng
#                      PATHS $ENV{MATLAB_ROOT}/bin $ENV{MATLAB_ROOT}/extern/lib
#                      PATH_SUFFIXES glnxa64 glnx86)
#
#        FIND_LIBRARY( MATLAB_MX_LIBRARY
#                      NAMES libmx mx
#                      PATHS $ENV{MATLAB_ROOT}/bin $ENV{MATLAB_ROOT}/extern/lib
#                      PATH_SUFFIXES glnxa64 glnx86)

        FIND_LIBRARY( MATLAB_ENGINE_LIBRARY
                      NAMES libMatlabEngine MatlabEngine
                      PATHS $ENV{MATLAB_ROOT}/extern/bin/glnxa64
                      PATHS SUFFIXES libMatlabEngine)

        FIND_LIBRARY( MATLAB_DATA_ARRAY_LIBRARY
                      NAMES libMatlabDataArray MatlabDataArray
                      PATHS $ENV{MATLAB_ROOT}/extern/bin/glnxa64
                      PATHS SUFFIXES libMatlabDataArray)

ENDIF("$ENV{MATLAB_ROOT}" STREQUAL "" )

# This is common to UNIX and Win32:
SET(MATLAB_LIBRARIES
#  ${MATLAB_MEX_LIBRARY}
#  ${MATLAB_MX_LIBRARY}
#  ${MATLAB_ENG_LIBRARY}
  ${MATLAB_ENGINE_LIBRARY}
  ${MATLAB_DATA_ARRAY_LIBRARY}
)

IF(MATLAB_INCLUDE_DIR AND MATLAB_LIBRARIES)
  SET(MATLAB_FOUND 1)
ENDIF(MATLAB_INCLUDE_DIR AND MATLAB_LIBRARIES)

MARK_AS_ADVANCED(
  MATLAB_LIBRARIES
#  MATLAB_ENG_LIBRARY
#  MATLAB_MEX_LIBRARY
#  MATLAB_MX_LIBRARY
  MATLAB_ENGINE_LIBRARY
  MATLAB_DATA_ARRAY_LIBRARY
  MATLAB_INCLUDE_DIR
  MATLAB_FOUND
  MATLAB_ROOT
)
