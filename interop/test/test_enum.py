# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
import pytest

from enum import Enum
from klr.frontend import Kernel

# Success cases
# (these functions should load and trace to KLR)

class E(Enum):
  x = 1
  y = 2
  z = 3

  def f(self):
    print(self.name + " " + str(self.value))

def enum1():
  e = E(name="x", value=1)
  assert e.name == "x"
  assert e.value == 1

def enum2():
  e = E.x
  assert e.name == "x"
  assert e.value == 1

def enum3():
  assert E.y.name == "y"
  assert E.y.value == 2

def enum4():
  assert E.z.name == "z"
  assert E.z.value == 3

def enumEq1():
  assert E.x == E.x

def enumEq2():
  assert E.x != E.y

def enumEq3():
  assert E.y != E.z

# test each function in turn
@pytest.mark.parametrize("f", [
  enum1,
  enum2,
  enum3,
  enum4,
  enumEq1,
  enumEq2,
  enumEq3,
  ])
def test_succeed(f):
  F = Kernel(f)   # parse python
  F.specialize()
  F.trace("tmp.klr")
  os.remove("tmp.klr")


# Boundary crossing
# Check objects that originate from Python

def cross1(e):
  assert e.name == "x"
  assert e.value == 1

def cross2(e):
  # technically this reference is crossing
  assert E.x.x.name == "x"

# test each function in turn
@pytest.mark.parametrize("f", [
  cross1,
  cross2,
  ])
def test_crossing(f):
  F = Kernel(f)   # parse python
  F.specialize((E.x,))
  F.trace("tmp.klr")
  os.remove("tmp.klr")
