# A simple Makefile for local development

PY_VER     ?= 3.10
PY_CFG     := $(shell which python${PY_VER}-config)
PY_EXT     := $(shell ${PY_CFG} --extension-suffix)
PY_DIR     := $(shell ${PY_CFG} --prefix)
#PY_CFLAGS  := $(shell ${PY_CFG} --cflags)
PY_CFLAGS  := -I${PY_DIR}/include/python${PY_VER}
PY_LDFLAGS := $(shell ${PY_CFG} --ldflags)
PY_LIBS    := "-lpython${PY_VER}"

CFLAGS := -std=c17 -Wall -Wextra
ifdef DEBUG
CFLAGS += -O0 -g
endif

C := cbor.c serde_common.c serde_python_core.c serde_file.c serde.c
C += region.c peg_parser.c gather.c frontend.c
O := $(patsubst %.c,%.${PY_VER}.o,$C)

TESTS := cbor_test

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

peg_parser.${PY_VER}.o: $(wildcard *.c)

%.${PY_VER}.o: %.c $(wildcard *.h)
	clang ${CFLAGS} ${PY_CFLAGS} -c $< -o $@

frontend${PY_EXT}: $(O)
	clang ${CFLAGS} $^ -dynamiclib -o $@ ${PY_LDFLAGS} ${PY_LIBS}

%_test: %_test.c %.c
	clang ${CFLAGS} ${PY_CFLAGS} $< -o $@
	./$@

# Simulate production build
load_test: *.cpp *.hpp region.c cbor.c
	gcc -std=c17 -Wall -c region.c cbor.c
	g++ --std=c++17 -Wall -o load_test load_test.cpp klir_serde.cpp klir_common.cpp cbor.o region.o
