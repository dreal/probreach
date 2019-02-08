# - Finding CAPD library
#  CAPD_FOUND - CAPD is found
#  CAPD_INCLUDE_DIR - CAPD include directories
#  CAPD_LIBRARIES - CAPD library



if(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
    set(CAPD_FOUND TRUE)
else(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)

    # finding include directories
    if(NOT CAPD_INCLUDE_DIR AND EXISTS /usr/include/capd)
        set(CAPD_INCLUDE_DIR /usr/include/capd)
    endif(NOT CAPD_INCLUDE_DIR AND EXISTS /usr/include/capd)
    if(NOT CAPD_INCLUDE_DIR AND EXISTS /usr/local/include/capd)
        set(CAPD_INCLUDE_DIR /usr/local/include/capd)
    endif(NOT CAPD_INCLUDE_DIR AND EXISTS /usr/local/include/capd)

    # finding libraries
    if(NOT CAPD_LIBRARIES AND EXISTS /usr/lib/libcapd.a)
        set(CAPD_LIBRARIES /usr/lib/libcapd.a)
    endif(NOT CAPD_LIBRARIES AND EXISTS /usr/lib/libcapd.a)
    if(NOT CAPD_LIBRARIES AND EXISTS /usr/local/lib/libcapd.a)
        set(CAPD_LIBRARIES /usr/local/lib/libcapd.a)
    endif(NOT CAPD_LIBRARIES AND EXISTS /usr/local/lib/libcapd.a)

    # checking if include directories and libraries has been found
    if(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
        set(CAPD_FOUND TRUE)
    endif(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
endif(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)

# reporting whether CAPD has been found
if(CAPD_FOUND)
    message(STATUS "Found CAPD (includes: ${CAPD_INCLUDE_DIR}, libs: ${CAPD_LIBRARIES})")
else(CAPD_FOUND)
    message(STATUS "CAPD not found")
endif(CAPD_FOUND)
