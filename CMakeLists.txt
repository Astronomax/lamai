cmake_minimum_required(VERSION 3.0)
project(lamai C)
set(CMAKE_C_STANDARD 11)

add_executable(lamai lamai.c)
target_compile_options(lamai PUBLIC -m32)

add_library(Runtime STATIC IMPORTED)
set_target_properties(Runtime PROPERTIES
        IMPORTED_LOCATION ${CMAKE_CURRENT_SOURCE_DIR}/runtime/runtime.a
        INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR}/runtime/
        INTERFACE_COMPILE_DEFINITIONS "USING_RUNTIME;RUNTIME_STATIC"
)

target_link_libraries(lamai PRIVATE Runtime)
target_link_options(lamai PUBLIC -m32)