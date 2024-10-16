# - Finding CAPD library. Variable that will be set if CAPD is found:
#
#       CAPD_FOUND - CAPD is found
#       CAPD_INCLUDE_DIR - CAPD include directories
#       CAPD_LIBRARIES - CAPD library

if(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
  set(CAPD_FOUND ON)
else(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)

  # searching for includes
  if(EXISTS ${CAPD_INSTALL_PATH}/include/capd)
    set(CAPD_INCLUDE_DIR "${CAPD_INSTALL_PATH}/include")
  endif(EXISTS ${CAPD_INSTALL_PATH}/include/capd)

  # searching for libraries
  if(EXISTS ${CAPD_INSTALL_PATH}/lib/libcapd.a)
    set(CAPD_LIBRARIES "${CAPD_INSTALL_PATH}/lib/libcapd.a")
  endif(EXISTS ${CAPD_INSTALL_PATH}/lib/libcapd.a)

  # checking if include directories and libraries has been found
  if(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
    set(CAPD_FOUND ON)
  endif(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)

endif(CAPD_INCLUDE_DIR AND CAPD_LIBRARIES)
