cmake_minimum_required(VERSION 3.10.0)
project("pardiff")

find_program(LLVM_CONFIG_BIN llvm-config-12)
if (NOT LLVM_CONFIG_BIN)
    find_program(LLVM_CONFIG_BIN llvm-config)
endif()

if (NOT LLVM_CONFIG_BIN)
    message(FATAL_ERROR "Can not find llvm-config, please put it in PATH or install llvm-12")
else()
    message(STATUS "LLVM_CONFIG_BIN : ${LLVM_CONFIG_BIN}")

    # version
    execute_process(COMMAND ${LLVM_CONFIG_BIN} --version OUTPUT_VARIABLE LLVM_VERSION)
    string(STRIP ${LLVM_VERSION} LLVM_VERSION)
    if(${LLVM_VERSION} VERSION_LESS "12.0.0")
        message(FATAL_ERROR "LLVM_VERSION: ${LLVM_VERSION} < 12.0.0. Please use 12.x.x")
    elseif(${LLVM_VERSION} VERSION_GREATER_EQUAL "13.0.0")
        message(FATAL_ERROR "LLVM_VERSION: ${LLVM_VERSION} >= 13.0.0. Please use 12.x.x")
    else()
        message(STATUS "LLVM_VERSION: ${LLVM_VERSION}")
    endif()

    # cflags
    execute_process(COMMAND ${LLVM_CONFIG_BIN} --cflags OUTPUT_VARIABLE LLVM_CFLAGS)
    string(STRIP ${LLVM_CFLAGS} LLVM_CFLAGS)
    message(STATUS "LLVM_CFLAGS: ${LLVM_CFLAGS}")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${LLVM_CFLAGS} -g")
    message(STATUS "CMAKE_C_FLAGS: ${CMAKE_C_FLAGS}")

    # cxxflags
    execute_process(COMMAND ${LLVM_CONFIG_BIN} --cxxflags OUTPUT_VARIABLE LLVM_CXXFLAGS)
    string(STRIP ${LLVM_CXXFLAGS} LLVM_CXXFLAGS)
    message(STATUS "LLVM_CXXFLAGS: ${LLVM_CXXFLAGS}")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_CXXFLAGS} -g -std=c++17 -fexceptions")
    message(STATUS "CMAKE_CXX_FLAGS: ${CMAKE_CXX_FLAGS}")

    # ldflags
    execute_process(COMMAND ${LLVM_CONFIG_BIN} --ldflags OUTPUT_VARIABLE LLVM_LDFLAGS)
    string(STRIP ${LLVM_LDFLAGS} LLVM_LDFLAGS)
    message(STATUS "LLVM_LDFLAGS: ${LLVM_LDFLAGS}")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LLVM_LDFLAGS}")

    # include_dir
    execute_process(COMMAND ${LLVM_CONFIG_BIN} --includedir OUTPUT_VARIABLE LLVM_INCLUDE_DIRS)
    string(STRIP ${LLVM_INCLUDE_DIRS} LLVM_INCLUDE_DIRS)
    message(STATUS "LLVM_INCLUDE_DIRS: ${LLVM_INCLUDE_DIRS}")
    include_directories(${LLVM_INCLUDE_DIRS})

    # link_dir
    execute_process(COMMAND ${LLVM_CONFIG_BIN} --libdir OUTPUT_VARIABLE LLVM_LIBRARY_DIRS)
    string(STRIP ${LLVM_LIBRARY_DIRS} LLVM_LIBRARY_DIRS)
    message(STATUS "LLVM_LIBRARY_DIRS: ${LLVM_LIBRARY_DIRS}")
    link_directories(${LLVM_LIBRARY_DIRS})
endif()

find_package(Z3 4.8.12)
if(NOT Z3_FOUND)
    message(FATAL_ERROR "Can not find z3-4.8.12 or higher, please install"
    "or pass `-DZ3_DIR=<path>` to the CMake invocation where"
    "`<path>` is the path to the directory containing this file.")
endif()
message(STATUS "Z3_VERSION : ${Z3_VERSION}" )
message(STATUS "Z3_C_INCLUDE_DIRS : ${Z3_C_INCLUDE_DIRS}")
message(STATUS "Z3_CXX_INCLUDE_DIRS : ${Z3_CXX_INCLUDE_DIRS}")
set(Z3_LINK_DIRS ${PACKAGE_PREFIX_DIR}/lib)
message(STATUS "Z3_LINK_DIRS : ${Z3_LINK_DIRS}")

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

include_directories(AFTER
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Z3_C_INCLUDE_DIRS}
        ${Z3_CXX_INCLUDE_DIRS}
        )
link_directories(BEFORE
        ${Z3_LINK_DIRS}
        )

#set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=address")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address")

add_subdirectory(lib)
add_subdirectory(tools)

