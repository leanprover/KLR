# tests of NKI allocation API

import os
import pytest

from apis import *

from klr import Kernel

# Success cases
# (these functions should load and trace to KLR)

def simple():
  ptr = nisa.sbuf_raw_ptr((0,0), (32,32))
  tensor1 = nl.ndarray((32,32), np.uint8, buffer=ptr, name="t")
  tensor2 = nl.ndarray((32,8), np.float32, buffer=ptr)

# test each function in turn
@pytest.mark.parametrize("f", [
  simple,
  ])
def test_succeed(f):
  F = Kernel(f)   # parse python
  file = F()      # specialize, and reduce to KLR
  os.remove(file)

# Failing cases
# (These functions are expected to fail elaboration to KLR)

def pdim_mismatch():
  ptr = nisa.sbuf_raw_ptr((0,0), (32,32))
  nl.ndarray((16,1), np.float32, buffer=ptr)

def too_large2():
  ptr = nisa.sbuf_raw_ptr((0,0), (32,32))
  nl.ndarray((32,16), np.float32, buffer=ptr)

@pytest.mark.parametrize("f", [
  pdim_mismatch,
  too_large2,
])
def test_fails(f):
  F = Kernel(f)
  with pytest.raises(Exception):
    F()
