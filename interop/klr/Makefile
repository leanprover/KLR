# A simple Makefile for local development

PY_VER     ?= 3.10
PY_CFG     := $(shell which python${PY_VER}-config)
PY_EXT     := $(shell ${PY_CFG} --extension-suffix)
PY_DIR     := $(shell ${PY_CFG} --prefix)
#PY_CFLAGS  := $(shell ${PY_CFG} --cflags)
PY_CFLAGS  := -I${PY_DIR}/include/python${PY_VER}
PY_LDFLAGS := $(shell ${PY_CFG} --ldflags)
PY_LIBS    := "-lpython${PY_VER}"

LEAN_CFLAGS  := $(shell leanc --print-cflags)
LEAN_LDFLAGS := -L$(shell lean --print-prefix)/lib $(shell leanc --print-ldflags)

CFLAGS := ${LEAN_CFLAGS} ${PY_CFLAGS}
LDFLAGS := ${KLR_LIBS} ${LEAN_LIBS} ${LEAN_LDFLAGS} ${PY_LDFLAGS} ${PY_LIBS}
CC := clang -std=c17 -g -Wall -Wextra -Wno-unused-command-line-argument

C := region.c peg_parser.c gather.c frontend.c klr_ffi.c
O := $(patsubst %.c,%.${PY_VER}.o,$C)

TESTS := cbor_test roundtrip_test klir_roundtrip_test

.SUFFIXES:
.PHONY: all versions test clean

all: frontend${PY_EXT} load_test

versions:
	$(MAKE) PY_VER=3.9
	$(MAKE) PY_VER=3.10
	$(MAKE) PY_VER=3.11
	$(MAKE) PY_VER=3.12
	$(MAKE) PY_VER=3.13

test: ${TESTS}

clean:
	rm -f *.o *.so
	rm -f ${TESTS}
	rm -f load_test
	rm -f roundtrip_test

peg_parser.${PY_VER}.o: $(wildcard *.c)

%.${PY_VER}.o: %.c $(wildcard *.h)
	${CC} ${CFLAGS} -c $< -o $@

# Lean dependencies
# build up KLR_A list with targets back to lake

D := ../../.lake
LAKE := lake -d ../..
P := ${D}/packages

# Main KLR library
A := ${D}/build/lib/libKLR.a
KLR_A := $A
$A:
	${LAKE} build

# TensorLib
A := ${P}/TensorLib/.lake/build/lib/libTensorLib.a
KLR_A += $A
$A:
	${LAKE} build TensorLib/TensorLib:static

# Plausible
A := ${P}/plausible/.lake/build/lib/libPlausible.a
KLR_A += $A
$A:
	${LAKE} build plausible/Plausible:static

# Aesop
A := ${P}/aesop/.lake/build/lib/libAesop.a
KLR_A += $A
$A:
	${LAKE} build aesop/Aesop:static

# Batteries
A := ${P}/batteries/.lake/build/lib/libBatteries.a
KLR_A += $A
$A:
	${LAKE} build batteries/Batteries:static

# for debugging
deps: ${KLR_A}
	@echo deps ${KLR_A}

# Python shared library
frontend${PY_EXT}: $(O) $(KLR_A)
	${CC} $^ -dynamiclib -o $@ ${LDFLAGS}

# Basic test oc CBOR utilities
cbor_test: cbor_test.c
	clang -std=c17 ${PY_CFLAGS} $< -o $@
	./$@

# Round trip tests for serialization/deserialization
klir_common_roundtrip_test: klir_common_roundtrip_test.cpp klir_common.cpp klir_common.hpp region.c cbor.c
	gcc -O0 -g -std=c17 -Wall -c region.c cbor.c
	g++ -O0 -g --std=c++17 -Wall -o klir_common_roundtrip_test klir_common_roundtrip_test.cpp klir_common.cpp cbor.o region.o

# KLIR round trip tests for serialization/deserialization
klir_roundtrip_test: klir_roundtrip_test.cpp klir_serde.cpp klir_common.cpp klir_common.hpp klir_serde.hpp region.c cbor.c
	gcc -O0 -g -std=c17 -Wall -c region.c cbor.c
	g++ -O0 -g --std=c++17 -Wall -o klir_roundtrip_test klir_roundtrip_test.cpp klir_serde.cpp klir_common.cpp cbor.o region.o

# Simulate production build
load_test: *.cpp *.hpp region.c cbor.c
	gcc -O0 -g -std=c17 -Wall -c region.c cbor.c
	g++ -O0 -g --std=c++17 -Wall -o load_test load_test.cpp klir_serde.cpp klir_common.cpp cbor.o region.o
