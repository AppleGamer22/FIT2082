cmake_minimum_required(VERSION 3.4.0)

# -------------------------------------------------------------------------------------------------------------------
#  -- Project information and versioning.

project(geas
        LANGUAGES CXX C)

# -------------------------------------------------------------------------------------------------------------------
#  -- Project build options

option(USE_ADDRESS_SANITIZER "Use GCC Address Sanitizer" OFF)

# -------------------------------------------------------------------------------------------------------------------
#  -- CMake initialisation

# Set build type when none is selected
set(DEFAULT_BUILD_TYPE "Release")
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    message(STATUS "Setting build type to '${DEFAULT_BUILD_TYPE}' as none was specified.")
    set(CMAKE_BUILD_TYPE "${DEFAULT_BUILD_TYPE}" CACHE STRING "Choose the type of build." FORCE)
    # Set the possible values of build type for cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS
        "Debug"
        "Release"
        "MinSizeRel"
        "RelWithDebInfo"
    )
endif()

# -------------------------------------------------------------------------------------------------------------------
#  -- Compiler configuration

set(CMAKE_CXX_STANDARD 11)

if(USE_ADDRESS_SANITIZER)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -fno-omit-frame-pointer")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=address")
endif()

if(APPLE)
    execute_process(COMMAND xcrun --show-sdk-path OUTPUT_VARIABLE OSX_SYSROOT OUTPUT_STRIP_TRAILING_WHITESPACE)
    set(CMAKE_OSX_SYSROOT ${OSX_SYSROOT})
    set(CMAKE_OSX_DEPLOYMENT_TARGET "10.9" CACHE STRING "Minimum OS X deployment version")
endif(APPLE)

# -------------------------------------------------------------------------------------------------------------------
#  -- Geas compilation targets.

include_directories(${PROJECT_SOURCE_DIR}/include)
# --- Libraries ---

add_library(geas_core OBJECT
    lib/engine/conflict.cc
    lib/engine/persist.cc
    lib/engine/propagator.cc
    lib/engine/state.cc
    lib/solver/branch.cc
    lib/solver/solver.cc
    lib/solver/solver_debug.cc
    lib/utils/MurmurHash3.cc
    lib/vars/fpvar.cc
    lib/vars/intvar.cc
)
add_library(geas_constraints OBJECT
    lib/constraints/flow/bipart.cc
    lib/constraints/alldifferent.cc
    lib/constraints/arith.cc
    lib/constraints/bool-linear.cc
    lib/constraints/cumulative.cc
    lib/constraints/difflogic.cc
    lib/constraints/disjunctive.cc
    lib/constraints/element.cc
    lib/constraints/linear.cc
    lib/constraints/linear-ps.cc
    lib/constraints/maximum.cc
    lib/constraints/mdd.cc
    lib/constraints/table.cc
    lib/constraints/values-precede.cc
)

# --- Distributables ---

# Geas C Library
add_library(geas
    lib/c/builtins.cc
    lib/c/geas.cc
    $<TARGET_OBJECTS:geas_core>
    $<TARGET_OBJECTS:geas_constraints>
)

install(
    TARGETS geas
    RUNTIME DESTINATION bin
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)
install(
    DIRECTORY include/geas
    DESTINATION include
)
