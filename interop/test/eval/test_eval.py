# This file tests the KLR evaluator

import numpy as np
import os
import pytest
import subprocess
import tempfile
import typing

DEBUG=True

def up(f, n):
    if n == 0:
        return f
    return up(os.path.dirname(f), n-1)

top = up(os.path.realpath(__file__), 4)
klr = top + '/bin/klr'

def call_lean(kernel : str, npy_inputs : list[np.ndarray], dir : str, outputs : list[str]) -> str:
  npy_files = []
  n = 0
  for t in npy_inputs:
    f = dir + "/input-" + str(n) + ".npy"
    np.save(f, t)
    npy_files.append(f)
  try:
    args = [klr, 'eval-klr', 'interop/test/eval/kernels.py', kernel]
    args += ["--output-names", ",".join(outputs)]
    args += ["--output-dir", dir]
    args += npy_files
    print("Running: " + " ".join(args))
    return subprocess.check_output(args, stderr=subprocess.STDOUT, cwd=top)
  finally:
    if not DEBUG:
      for f in npy_files:
        os.remove(f)

def test_kernel1():
  inp = np.arange(10, dtype='float32').reshape(2, 5)
  expected = np.arange(10, dtype='float32').reshape(2, 5) + 1
  temp_dir = tempfile.mkdtemp()
  call_lean("kernel1", [inp], temp_dir, ["b"])
  b = np.load(temp_dir + "/b.npy")
  assert np.array_equal(b, expected)
  #TODO: remove temp dirs

def test_kernel2():
  inp = np.arange(10, dtype='float32').reshape(2, 5)
  expected = np.arange(10, dtype='float32').reshape(2, 5) - 5
  temp_dir = tempfile.mkdtemp()
  call_lean("kernel2", [inp], temp_dir, ["b"])
  b = np.load(temp_dir + "/b.npy")
  assert np.array_equal(b, expected)

def test_kernel3():
  inp = np.arange(10, dtype='float32').reshape(2, 5)
  expected = np.arange(10, dtype='float32').reshape(2, 5) * 5
  temp_dir = tempfile.mkdtemp()
  call_lean("kernel3", [inp], temp_dir, ["b"])
  b = np.load(temp_dir + "/b.npy")
  assert np.array_equal(b, expected)

def test_kernel4():
  inp = np.arange(10, dtype='float32').reshape(2, 5)
  expected = (np.arange(10, dtype='float32').reshape(2, 5) * 5) - 1
  temp_dir = tempfile.mkdtemp()
  call_lean("kernel4", [inp], temp_dir, ["b"])
  b = np.load(temp_dir + "/b.npy")
  assert np.array_equal(b, expected)

def test_kernel5():
  inp = np.arange(10, dtype='float32').reshape(2, 5)
  expected = 1 - (np.arange(10, dtype='float32').reshape(2, 5) * 5)
  temp_dir = tempfile.mkdtemp()
  call_lean("kernel5", [inp], temp_dir, ["b"])
  b = np.load(temp_dir + "/b.npy")
  assert np.array_equal(b, expected)

def test_kernel6():
  inp = np.arange(10, dtype='float32').reshape(2, 5)
  expected = 1 - (5 - np.arange(10, dtype='float32').reshape(2, 5))
  temp_dir = tempfile.mkdtemp()
  call_lean("kernel6", [inp], temp_dir, ["b"])
  b = np.load(temp_dir + "/b.npy")
  assert np.array_equal(b, expected)

