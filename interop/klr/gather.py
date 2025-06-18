# Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import sys
import importlib
import klr.frontend as fe

# This script is used internally by the klr binary.

def gather(module, fn, outfile):
  m = importlib.import_module(module)
  f = getattr(m, fn)
  F = fe.Kernel(f)
  F._serialize_python(outfile)

if len(sys.argv) != 4:
  print(f"Usage: {sys.argv[0]} module function outfile", file=sys.stderr)
  sys.exit(1)

_, m, fn, outfile = sys.argv
try: gather(m, fn, outfile)
except Exception as e:
  print(str(e), file=sys.stderr)
  sys.exit(1)
