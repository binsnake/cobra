cmake_minimum_required(VERSION 3.20)
project(cobra-parity-cpp LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(
    COBRA_CPP_SOURCE
    "D:/binsnake/CoBRA-cpp"
    CACHE PATH
    "Path to a CoBRA C++ source checkout"
)
option(
    COBRA_PARITY_ENABLE_SIG_STATS
    "Enable upstream signature-evaluation counters in the parity runner"
    OFF
)
option(
    COBRA_PARITY_ENABLE_TRACE
    "Enable upstream pipeline trace output in the parity runner"
    OFF
)

if(NOT EXISTS "${COBRA_CPP_SOURCE}/lib/core/CMakeLists.txt")
    message(FATAL_ERROR "COBRA_CPP_SOURCE is not a CoBRA C++ checkout: ${COBRA_CPP_SOURCE}")
endif()

# Keep the dependency build focused on cobra-core. The upstream CLI is still
# declared by its top-level project, but it is excluded from the default build.
set(COBRA_BUILD_LLVM_PASS OFF CACHE BOOL "" FORCE)
set(COBRA_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(COBRA_ENABLE_TRACE ${COBRA_PARITY_ENABLE_TRACE} CACHE BOOL "" FORCE)
set(COBRA_ENABLE_SIG_STATS ${COBRA_PARITY_ENABLE_SIG_STATS} CACHE BOOL "" FORCE)
set(COBRA_ENABLE_TRACY OFF CACHE BOOL "" FORCE)
add_subdirectory("${COBRA_CPP_SOURCE}" "${CMAKE_BINARY_DIR}/cobra-upstream" EXCLUDE_FROM_ALL)

add_executable(
    cobra-parity-cpp
    main.cpp
    "${COBRA_CPP_SOURCE}/tools/cobra-cli/ExprParser.cpp"
)
target_include_directories(
    cobra-parity-cpp
    PRIVATE "${COBRA_CPP_SOURCE}/tools/cobra-cli"
)
target_link_libraries(cobra-parity-cpp PRIVATE cobra-core)
