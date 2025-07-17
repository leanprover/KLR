#!/bin/bash

PY=python3.10
PYSRC=$PYSRC

$PYSRC/Parser/asdl_c.py -d $PYSRC/Parser/Python.asdl \
  -C peg_parser/ast_python.c -H ast_python.h -I ignored
rm ignored

$PY $PYSRC/Tools/build/generate_token.py h peg_parser/Tokens tmp1
$PY $PYSRC/Tools/build/generate_token.py c peg_parser/Tokens tmp2
cat tmp1 tmp2 > peg_parser/token.c
rm tmp1 tmp2

PYTHONPATH=$PYSRC/Tools/peg_generator \
  $PY -m pegen -q c peg_parser/python.gram peg_parser/Tokens -o peg_parser/parser.c
