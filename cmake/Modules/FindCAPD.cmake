# - Finding CAPD library
#  CAPD_FOUND - CAPD is found
#  CAPD_INCLUDE_DIR - CAPD include directories
#  CAPD_LIBRARIES - CAPD library

set(CAPD_INCLUDE_DIR_LIST ${CAPD_INCLUDE_DIR_LIST} /usr/capd/include)
set(CAPD_INCLUDE_DIR_LIST ${CAPD_INCLUDE_DIR_LIST} /usr/local/capd/include)

#set(CAPD_LIBRARIES_LIST ${CAPD_LIBRARIES_LIST} /usr/capd/lib/libcapd-gui.a)
#set(CAPD_LIBRARIES_LIST ${CAPD_LIBRARIES_LIST} /usr/local/capd/lib/libcapd-gui.a)

set(CAPD_LIBRARIES_LIST ${CAPD_LIBRARIES_LIST} /usr/capd/lib/libcapd.a)
set(CAPD_LIBRARIES_LIST ${CAPD_LIBRARIES_LIST} /usr/local/capd/lib/libcapd.a)

if(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
    set(CAPD_FOUND TRUE)
else(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)

    # finding include directories
    foreach(ITEM ${CAPD_INCLUDE_DIR_LIST})
        if(EXISTS ${ITEM} AND NOT CAPD_INCLUDE_DIR)
            set(CAPD_INCLUDE_DIR ${ITEM})
        endif(EXISTS ${ITEM} AND NOT CAPD_INCLUDE_DIR)
    endforeach(ITEM)

    # finding libraries
    foreach(ITEM ${CAPD_LIBRARIES_LIST})
        if(EXISTS ${ITEM} AND NOT CAPD_LIBRARIES)
            set(CAPD_LIBRARIES ${ITEM})
        endif(EXISTS ${ITEM} AND NOT CAPD_LIBRARIES)
    endforeach(ITEM)

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
