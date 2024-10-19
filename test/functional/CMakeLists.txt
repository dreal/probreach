configure_file(
  "${CMAKE_CURRENT_LIST_DIR}/test_env.h.in"
  "${CMAKE_CURRENT_LIST_DIR}/test_env.h")

include_directories(${CMAKE_CURRENT_LIST_DIR})

include("${CMAKE_CURRENT_LIST_DIR}/formal/CMakeLists.txt")
