"""
Copyright (C) 2025, Amazon.com. All Rights Reserved

"""
import unittest
from apis import *

"""
Unit tests for tensor_scalar.

If using these tests for development, you can generate the NKI.json from
the top-level like so:

  PYTHONPATH=interop:interop/test ./bin/gather test_nki_isa_tensor_scalar.kernel1 > kernel1.json

and then, e.g.

  lake exe klr trace kernel1.json
  lake exe klr compile kernel1.json
"""

# utility function - allocate memory in DRAM
def alloc_like(t):
  return nl.ndarray(t.shape, dtype=t.dtype, buffer=nl.shared_hbm)

# utility function - allocate memory in DRAM and copy SBUF tile to it
def dram_tile(a):
  b = alloc_like(a)
  nl.store(b, a)
  return b

# test kernel 1 : t - 1.0 with no access pattern
def kernel1(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.subtract, 1.0)
  return dram_tile(b_tile)

# test kernel 2 : t - 1.0 with ellipsis access pattern
def kernel2(a):
  a_tile = nl.load(a[...])
  b_tile = nisa.tensor_scalar(a_tile, np.subtract, 1.0)
  return dram_tile(b_tile)

# test kernel 2 : t - 1.0 with simple tile access pattern
def kernel3(a):
  a_tile = nl.load(a[0:128,0:512])
  b_tile = nisa.tensor_scalar(a_tile, np.subtract, 1.0)
  return dram_tile(b_tile)

# The above example will fail tracing with:
#  nl.store(b, b_tile)
#              ^-- incompatible shapes [10, 10] [128, 512]
# This is because inferArguments is very dumb.
# You can use the kernel below for testing to get proper arguments.
def kernel3b():
  a = nl.ndarray((128,512), dtype="float32", buffer=nl.shared_hbm)
  return kernel3(a)

def tensor_scalar(dst, src, op, scalar):
  src_tile = nl.load(src)
  dst_tile = nisa.tensor_scalar(src_tile, op, 1.0)
  nl.store(dst, dst_tile)

def kernel4(a):
  b = alloc_like(a)
  for x in range(4):
    tensor_scalar(b[x,0:10], a[x,0:10], np.subtract, 1.0)
  return b
