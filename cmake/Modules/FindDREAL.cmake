# - Finding dReal package
#  DREAL_FOUND - dReal and all required
#  DREAL_INCLUDE_DIR - dReal include directories
#  DREAL_LIBRARIES - neccessary libraries produced while building dReal
#  DREAL_EXE - dReal executable

# add /usr/local/ to look for includes, libraries and binaries

# trying different directories
set(DREAL_DIRS ${DREAL_DIRS} $ENV{HOME}/dreal)
set(DREAL_DIRS ${DREAL_DIRS} $ENV{HOME}/dreal3)
set(DREAL_DIRS ${DREAL_DIRS} /usr/src/dreal)
set(DREAL_DIRS ${DREAL_DIRS} /usr/src/dreal3)
set(DREAL_DIRS ${DREAL_DIRS} /usr/local/src/dreal)
set(DREAL_DIRS ${DREAL_DIRS} /usr/local/src/dreal3)
# trying different build directories
set(BUILD_DIRS ${BUILD_DIRS} build/release)
set(BUILD_DIRS ${BUILD_DIRS} build/minsizerel)
set(BUILD_DIRS ${BUILD_DIRS} build/debug)
set(BUILD_DIRS ${BUILD_DIRS} Release)
set(BUILD_DIRS ${BUILD_DIRS} MinSizeRel)
set(BUILD_DIRS ${BUILD_DIRS} Debug)

if(DREAL_INCLUDE_DIR AND DREAL_LIBRARIES)
    set(DREAL_FOUND TRUE)
else(DREAL_INCLUDE_DIR AND DREAL_LIBRARIES)
    # going through possible dReal directories
    foreach(DREAL_DIR ${DREAL_DIRS})
        foreach(BUILD ${BUILD_DIRS})
            # finding include directory
            if(EXISTS ${DREAL_DIR}/${BUILD}/include)
                # setting include directory
                if(NOT DREAL_INCLUDE_DIR)
                    set(DREAL_INCLUDE_DIR ${DREAL_DIR}/${BUILD}/include)
                endif(NOT DREAL_INCLUDE_DIR)
            endif(EXISTS ${DREAL_DIR}/${BUILD}/include)
            # finding libraries directory
            if(EXISTS ${DREAL_DIR}/${BUILD}/lib)
                # finding CAPD
                if(NOT CAPD_LIBRARIES AND EXISTS ${DREAL_DIR}/${BUILD}/lib/libcapd.a)
                    set(CAPD_LIBRARIES ${DREAL_DIR}/${BUILD}/lib/libcapd.a)
                endif(NOT CAPD_LIBRARIES AND EXISTS ${DREAL_DIR}/${BUILD}/lib/libcapd.a)
                # finding IBEX
                if(NOT IBEX_LIBRARIES AND EXISTS ${DREAL_DIR}/${BUILD}/lib/libibex.a)
                    set(IBEX_LIBRARIES ${DREAL_DIR}/${BUILD}/lib/libibex.a)
                endif(NOT IBEX_LIBRARIES AND EXISTS ${DREAL_DIR}/${BUILD}/lib/libibex.a)
                # finding PRIM
                if(NOT PRIM_LIBRARIES AND EXISTS ${DREAL_DIR}/${BUILD}/lib/libprim.a)
                    set(PRIM_LIBRARIES ${DREAL_DIR}/${BUILD}/lib/libprim.a)
                endif(NOT PRIM_LIBRARIES AND EXISTS ${DREAL_DIR}/${BUILD}/lib/libprim.a)
                # setting libraries
                if(NOT DREAL_LIBRARIES)
                    if(CAPD_LIBRARIES AND IBEX_LIBRARIES AND PRIM_LIBRARIES)
                        set(DREAL_LIBRARIES ${DREAL_LIBRARIES} ${CAPD_LIBRARIES})
                        set(DREAL_LIBRARIES ${DREAL_LIBRARIES} ${IBEX_LIBRARIES})
                        set(DREAL_LIBRARIES ${DREAL_LIBRARIES} ${PRIM_LIBRARIES})
                    endif(CAPD_LIBRARIES AND IBEX_LIBRARIES AND PRIM_LIBRARIES)
                endif(NOT DREAL_LIBRARIES)
            endif(EXISTS ${DREAL_DIR}/${BUILD}/lib)
            # finding dReal executable
            if(NOT DREAL_EXE AND EXISTS ${DREAL_DIR}/${BUILD}/dReal)
                set(DREAL_EXE ${DREAL_DIR}/${BUILD}/dReal)
            endif(NOT DREAL_EXE AND EXISTS ${DREAL_DIR}/${BUILD}/dReal)
        endforeach(BUILD)
    endforeach(DREAL_DIR)
    # checking if include directories and libraries has been found
    if(DREAL_INCLUDE_DIR AND DREAL_LIBRARIES)
        set(DREAL_FOUND TRUE)
    endif(DREAL_INCLUDE_DIR AND DREAL_LIBRARIES)
endif(DREAL_INCLUDE_DIR AND DREAL_LIBRARIES)

# reporting that dReal has been found
if(DREAL_FOUND)
    message(STATUS "Found dReal (includes: ${DREAL_INCLUDE_DIR}, libs: ${DREAL_LIBRARIES})")
else(DREAL_FOUND)
    message(STATUS "dReal not found")
endif(DREAL_FOUND)

# setting solver executable
if(NOT DREAL_EXE)
    message(STATUS "dReal executable not found. DREAL_EXE=dReal will be set")
    set(DREAL_EXE dReal)
else(NOT DREAL_EXE)
    message(STATUS "Found dReal executable: ${DREAL_EXE}")
endif(NOT DREAL_EXE)