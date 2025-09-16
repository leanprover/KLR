# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
import pytest

from klr.frontend import Kernel

# Success cases
# (these functions should load and trace to KLR)

class A:
  x : int = 1
  y : bool

  def check(self, x, y):
    assert self.x == x
    assert self.y == y

  def set_x(self, x): self.x = x
  def set_y(self, y): self.y = y

# default initializer
def init1():
  a = A()
  assert a.x == 1
  assert a.y == None
  a.check(1, None)

# all positional arguments
def init2():
  a = A(3, False)
  a.check(3, False)

# all keyword arguments
def init3():
  a = A(y=55, x=12)
  a.check(12, 55)

# partial keyword aguments
def init4():
  a = A(y=9)
  a.check(1, 9)

# partial keyword aguments
def init5():
  a = A(x=9)
  a.check(9, None)

#partial positional arguments
def init6():
  a = A(9)
  a.check(9, None)

# modify within method
def modify1():
  a = A()
  a.set_x(10)
  a.set_y(11)
  a.check(10, 11)

# modify direct
def modify2():
  a = A()
  a.y = a.x + 1
  a.check(1, 2)

# Check manually written init functions
class B:
  x : int
  def __init__(self, x=1):
    self.x = x

def init_b1():
  b = B()
  assert b.x == 1

def init_b2():
  b = B(2)
  assert b.x == 2

# Check the classes as fields work properly
class C:
  b : B = B()

def init_c1():
  c = C()
  assert c.b.x == 1

class D:
  b : B = B(10)

def init_d1():
  d = D()
  assert d.b.x == 10

# test dynamic attributes

class E():
  pass

def dynamic1():
  e = E()
  e.x = 1
  assert e.x == 1

# test each function in turn
@pytest.mark.parametrize("f", [
  init1,
  init2,
  init3,
  init4,
  init5,
  init6,
  modify1,
  modify2,
  init_b1,
  init_b2,
  init_c1,
  init_d1,
  dynamic1,
  ])
def test_succeed(f):
  F = Kernel(f)   # parse python
  F.specialize()
  F.trace("tmp.klr")
  os.remove("tmp.klr")


# Failing cases
# (These functions are expected to fail elaboration to KLR)

def bad_init1():
  A(1,2,3)

def bad_attribute():
  a = A()
  a.unknown

@pytest.mark.parametrize("f", [
  bad_init1,
  bad_attribute,
])
def test_fails(f):
  with pytest.raises(Exception):
    F = Kernel(f)
    F.specialize()
    F.trace("tmp.klr")
    os.remove("tmp.klr")
