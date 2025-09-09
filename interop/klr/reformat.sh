#!/bin/bash
set -e -u -o pipefail
trap "kill 0" SIGINT SIGTERM

for f in klir_*.[hc]pp
do
  clang-format -i $f
done
