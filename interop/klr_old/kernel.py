# Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import os
import subprocess
import tempfile
import types

from typing import Tuple, Optional
from importlib.resources import files

from .parser import Parser

def up(f, n):
  d = os.path.dirname(f)
  for _ in range(n):
    d = os.path.dirname(d)
  return d

def find_klr(): # -> Union[pathlib.PosixPath,str]
  # For development, pick up the klr binary from the project dir
  project_root = up(os.path.abspath(__file__), 2)
  bin = project_root + '/bin/klr'
  if not os.path.isfile(bin):
    # For regular pip users, pick up the klr from the wheel. While the type of `bin` here is
    # PosixPath rather than string, they both work as the first argument to subprocess.run
    # FIXME: the .. is because the wheel puts klr and bin at the same level in the
    # directory hierarchy, this seems incorrect. Perhaps should use the scripts directory?
    # see https://packaging.python.org/en/latest/specifications/binary-distribution-format/
    bin = files('klr').joinpath('../bin/klr')
  return bin

# This function will return the name of the generated file and
# any warnings from the tracing process. If an error occurs,
# the file name will be None.
def run_klr(infile, outdir=None) -> Tuple[Optional[str],str]:
  bin = find_klr()
  args = [bin, 'trace-api', infile.name]
  if outdir:
    args += ['-d', outdir]
  try:
    cp = subprocess.run(args, capture_output=True, check=True)
    return cp.stdout.decode().strip(), cp.stderr.decode().strip()
  except subprocess.CalledProcessError as e:
    return None, e.stderr.decode().strip()

class Kernel:
  def __init__(self, f : types.FunctionType, outdir=None):
    super().__init__()
    self.parser = Parser(f)
    self.outdir = outdir

  def specialize(self, *args, **kwargs):
    self.parser.apply_args(*args, **kwargs)

  def gather(self) -> str:
    return self.parser.json()

  def trace(self, outdir=None) -> Tuple[Optional[str],str]:
    outdir = outdir or self.outdir
    json_kernel = self.parser.json()
    # temp_file will be deleted
    with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as temp_file:
      temp_file.write(json_kernel)
      temp_file.flush()
      return run_klr(temp_file, outdir=outdir)

  def __call__(self, *args, **kwargs):
    self.specialize(*args, **kwargs)
    klr_file, warnings = self.trace()
    if klr_file is None:
      raise Exception(warnings)
    return klr_file

# @klr attribute
def klr(f=None, outdir=None):
  if f is None:
    return lambda f: Kernel(f, outdir)
  else:
    return Kernel(f)
