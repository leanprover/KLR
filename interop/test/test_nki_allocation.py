# tests of NKI allocation API

import os
import pytest

from apis import *

from klr import Kernel

# Success cases
# (these functions should load and trace to KLR)

def simple():
  tensor1 = nl.ndarray((32,32), np.uint8, buffer=nl.sbuf, name="t")
  tensor2 = nl.ndarray((32,8), np.float32, buffer=nl.sbuf)

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

def too_large():
  nl.ndarray((512,16), np.float32, buffer=nl.sbuf)

@pytest.mark.parametrize("f", [
  too_large,
])
def test_fails(f):
  F = Kernel(f)
  with pytest.raises(Exception):
    F()
