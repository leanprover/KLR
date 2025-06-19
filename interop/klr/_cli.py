# Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import importlib
import importlib.resources
import klr.frontend as fe
import os
import subprocess
import sys

# This function is only used from within a pip-installed environment
# Local developers can use ./bin/klr from the github root
def run_klr():
  # FIXME: Perhaps should use the scripts directory? How do we do that?
  # see https://packaging.python.org/en/latest/specifications/binary-distribution-format/
  bin = importlib.resources.files('klr').joinpath('klr.bin')
  args = [bin] + sys.argv[1:]
  cp = subprocess.run(args)
  sys.exit(cp.returncode)

# This function is used internally by the klr binary.
# For a pip-installed environment, this is available as script "klr-gather"
# For local developers, this is called by ./bin/klr-gather
def gather():
  if len(sys.argv) != 4:
    print(f"Usage: {sys.argv[0]} module function outfile", file=sys.stderr)
    sys.exit(1)

  _, module, fn, outfile = sys.argv
  try:
    m = importlib.import_module(module)
    f = getattr(m, fn)
    F = fe.Kernel(f)
    F._serialize_python(outfile)
  except Exception as e:
    print(str(e), file=sys.stderr)
    sys.exit(1)
