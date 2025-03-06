# tests of pointers and memory allocation

import os
from apis import *

# this needs to be after the apis
import numpy as np
import pytest

from klr import Kernel

# Success cases
# (these functions should load and trace to KLR)

def pointers():
  x = sbuf[0:128, 0:512]
  y = x[32:,:]
  a = pmem[:64,:512]
  b = a[32:,:]
  sb = sbuf[:,1024:2048]
  left = sb[:,0:512]
  right = sb[:,512:]
  big = sbuf[None,:]

# test each function in turn
@pytest.mark.parametrize("f", [
  pointers,
  ])
def test_succeed(f):
  F = Kernel(f)   # parse python
  file = F()      # specialize, and reduce to KLR
  os.remove(file)

# Failing cases
# (These functions are expected to fail elaboration to KLR)

def bad_pointer1(): sbuf[1:,0:512]   # sbuf must start at 0,32,64, or 96
def bad_pointer2(): sbuf[0:32,5:32]  # starts must be even
def bad_pointer3(): sbuf[None,0:511] # ends must be even
def bad_pointer4(): sbuf[None,0:0x50000] # too big free dim
def bad_pointer5(): sbuf[0:130,0:512] # too big pdim

@pytest.mark.parametrize("f", [
  bad_pointer1,
  bad_pointer2,
  bad_pointer3,
  bad_pointer4,
  bad_pointer5,
])
def test_fails(f):
  F = Kernel(f)
  with pytest.raises(Exception):
    F()
