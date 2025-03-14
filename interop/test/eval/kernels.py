import nki.isa as nisa
import nki.language as nl
import numpy as np

# t + 1.0 with no access pattern
def kernel1(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.add, 1.0)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.sbuf)
  nl.store(b, b_tile)
  return b

# t - 5.0 with no access pattern
def kernel2(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.subtract, 5.0)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.sbuf)
  nl.store(b, b_tile)
  return b

# t * 5.0 with no access pattern
def kernel3(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.multiply, 5.0)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.sbuf)
  nl.store(b, b_tile)
  return b

# t * 5.0 - 1 with no access pattern
def kernel4(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.multiply, 5.0, False, np.subtract, 1.0, False)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.sbuf)
  nl.store(b, b_tile)
  return b

# 1 - t * 5.0 with no access pattern
def kernel5(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.multiply, 5.0, False, np.subtract, 1.0, True)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.sbuf)
  nl.store(b, b_tile)
  return b

# 1 - (5.0 - t) with no access pattern
def kernel6(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.subtract, 5.0, True, np.subtract, 1.0, True)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.sbuf)
  nl.store(b, b_tile)
  return b
