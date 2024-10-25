# - Finding dReal package
#  DREAL_FOUND - dReal and all required
#  DREAL_WORKS - dReal works with a simple run (i.e., "--version" flag)
#  DREAL_VERSION - dReal version
#  DREAL_BIN_PATH - dReal executable path

# trying different locations
set(DREAL_BIN_PATHS ${DREAL_BIN_PATHS} ${DREAL_EXTERNAL_BIN_PATH})
set(DREAL_BIN_PATHS ${DREAL_BIN_PATHS} "/usr/bin/dReal")
set(DREAL_BIN_PATHS ${DREAL_BIN_PATHS} "/usr/local/bin/dReal")

foreach(CUR_DREAL_BIN_PATH ${DREAL_BIN_PATHS})
  if(EXISTS ${CUR_DREAL_BIN_PATH})
    set(DREAL_FOUND ON)
    execute_process(
      COMMAND ${CUR_DREAL_BIN_PATH} "--version"
      RESULT_VARIABLE DREAL_EXE_RESULT
      OUTPUT_VARIABLE DREAL_VERSION
      )
    if(${DREAL_EXE_RESULT} EQUAL 0)
      set(DREAL_WORKS ON)
      set(DREAL_BIN_PATH ${CUR_DREAL_BIN_PATH})
      break()
    endif(${DREAL_EXE_RESULT} EQUAL 0)
  endif(EXISTS ${CUR_DREAL_BIN_PATH})
endforeach(CUR_DREAL_BIN_PATH ${DREAL_BIN_PATHS})

