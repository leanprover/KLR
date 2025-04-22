#!/bin/bash
set -e -u -o pipefail
trap "kill 0" SIGINT SIGTERM

# Header files have to be processsed from stdin to get clang-format
# to use the correct language
for f in ast_*.h
do
  clang-format --assume-filename="tmp.c" < $f > tmp.h
  mv tmp.h $f
done

#clang-format -i *.c
