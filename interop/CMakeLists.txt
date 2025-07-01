# 3.30 because that's the latest in Brazil as of June 2025.
# 
# "3.30...4.0" means "Requires CMake 3.30, known to work fine with CMake up to 4.0,
# and if building with CMake even newer than that, use with policy defaults from 4.0."
cmake_minimum_required(VERSION 3.30...4.0)

project(
    ${SKBUILD_PROJECT_NAME}
    VERSION ${SKBUILD_PROJECT_VERSION}
    LANGUAGES C
)

find_package(
    Python REQUIRED
    COMPONENTS Interpreter Development.Module
)

add_subdirectory(klr)
