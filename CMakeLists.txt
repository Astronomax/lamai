cmake_minimum_required(VERSION 3.0)
project(lamai)
set(CMAKE_CXX_STANDARD 17)

add_executable(lamai lamai.cpp)
target_compile_options(lamai PUBLIC -m32)
add_custom_target(BuildRuntime ALL
        COMMAND make
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/runtime
)
add_library(Runtime STATIC IMPORTED)
set_target_properties(Runtime PROPERTIES
        IMPORTED_LOCATION ${CMAKE_CURRENT_SOURCE_DIR}/runtime/runtime.a
        INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR}/runtime/runtime.h
        INTERFACE_COMPILE_DEFINITIONS "USING_RUNTIME;RUNTIME_STATIC"
)
add_dependencies(Runtime BuildRuntime)

target_link_libraries(lamai PRIVATE Runtime)
target_link_options(lamai PUBLIC -m32)