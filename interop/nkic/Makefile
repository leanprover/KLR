# A simple Makefile for local development

PY_VER     ?= 3.10
PY_CFG     := $(shell which python${PY_VER}-config)
PY_EXT     := $(shell ${PY_CFG} --extension-suffix)
PY_DIR     := $(shell ${PY_CFG} --prefix)
#PY_CFLAGS  := $(shell ${PY_CFG} --cflags)
PY_CFLAGS  := -I${PY_DIR}/include/python${PY_VER}
PY_LDFLAGS := $(shell ${PY_CFG} --ldflags)
PY_LIBS    := "-lpython${PY_VER}"

C := region.c peg_parser.c gather.c frontend.c
O := $(patsubst %.c,%.${PY_VER}.o,$C)

TESTS := cbor_test

.SUFFIXES:
.PHONY: all versions test clean

all: frontend${PY_EXT}

versions:
	$(MAKE) PY_VER=3.9
	$(MAKE) PY_VER=3.10
	$(MAKE) PY_VER=3.11
	$(MAKE) PY_VER=3.12

test: ${TESTS}

clean:
	rm -f *.o *.so
	rm -f ${TESTS}

peg_parser.${PY_VER}.o: $(wildcard *.c)

%.${PY_VER}.o: %.c $(wildcard *.h)
	clang -std=c17 -Wall -Wextra ${PY_CFLAGS} -c $< -o $@

frontend${PY_EXT}: $(O)
	clang -std=c17 $^ -dynamiclib -o $@ ${PY_LDFLAGS} ${PY_LIBS}

%_test: %_test.c %.c
	clang -std=c17 -Wall -Wextra $< -o $@
	./$@
