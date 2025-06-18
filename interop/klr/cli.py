# Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import os
import subprocess
import sys

from importlib.resources import files

# This code is only used from within a pip-installed environment
# Local developers can use ./bin/klr from the github root

# FIXME: Perhaps should use the scripts directory? How do we do that?
# see https://packaging.python.org/en/latest/specifications/binary-distribution-format/
bin = files('klr').joinpath('klr.bin')

# call KLR binary
args = [bin] + sys.argv[1:]
cp = subprocess.run(args)
sys.exit(cp.returncode)
