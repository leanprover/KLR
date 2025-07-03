# Files with no Python dependency, that can be build into the standalone unit tests
set(CORE_FILES
    cbor.c
    region.c
    serde_common.c
    serde_file.c
    serde_nki.c
    serde_python_core.c
    serde.c
    simplify.c
)

# Declare Python C extension module
Python_add_library(frontend MODULE WITH_SOABI
    ${CORE_FILES}
    # Files with dependency on Python C API
    frontend.c
    gather.c
    peg_parser.c
    topy_nki.c
)

install(
    TARGETS frontend
    DESTINATION klr/
)

if(BUILD_TESTING)

    # cbor_test
    add_executable(cbor_test
        ${CORE_FILES}
        cbor_test.c
    )
    add_test(
        NAME cbor_test
        COMMAND cbor_test
    )

    # simplify_test
    add_executable(simplify_test
        ${CORE_FILES}
        simplify_test.c
    )
    add_test(
        NAME simplify_test
        COMMAND simplify_test
    )

endif()
