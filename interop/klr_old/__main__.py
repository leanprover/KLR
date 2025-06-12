# Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import copy
import importlib.resources as res
import sys
import subprocess

from .kernel import find_klr

# call KLR binary
args = [find_klr()] + sys.argv[1:]
cp = subprocess.run(args)
sys.exit(cp.returncode)
