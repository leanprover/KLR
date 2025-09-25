# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
import pytest

from runner import *

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

# test class fields

def cls_fields1():
  assert A.x == 1

def cls_fields2():
  assert C.b.x == 1

def cls_methods():
  a = A()
  A.check(a, 1, None)

# overloading

class LeftOver:
  def __eq__(self, x): return 1
  def __ne__(self, x): return 2
  def __lt__(self, x): return 3
  def __le__(self, x): return 4
  def __gt__(self, x): return 5
  def __ge__(self, x): return 6

  def __add__(self, x): return 10
  def __sub__(self, x): return 11
  def __mul__(self, x): return 12
  def __truediv__(self, x): return 13
  def __mod__(self, x): return 14
  def __pow__(self, x): return 15
  def __floordiv__(self, x): return 16

  def __lshift__(self, x): return 20
  def __rshift__(self, x): return 21
  def __or__(self, x): return 22
  def __xor__(self, x): return 23
  def __and__(self, x): return 24

class RightOver:
  def __req__(self, x): return 1
  def __rne__(self, x): return 2
  def __rlt__(self, x): return 3
  def __rle__(self, x): return 4
  def __rgt__(self, x): return 5
  def __rge__(self, x): return 6

  def __radd__(self, x): return 10
  def __rsub__(self, x): return 11
  def __rmul__(self, x): return 12
  def __rtruediv__(self, x): return 13
  def __rmod__(self, x): return 14
  def __rpow__(self, x): return 15
  def __rfloordiv__(self, x): return 16

  def __rlshift__(self, x): return 20
  def __rrshift__(self, x): return 21
  def __ror__(self, x): return 22
  def __rxor__(self, x): return 23
  def __rand__(self, x): return 24

def overload1():
  x = LeftOver()
  y = 1
  assert (x == y) == 1
  assert (x != y) == 2
  assert (x <  y) == 3
  assert (x <= y) == 4
  assert (x >  y) == 5
  assert (x >= y) == 6

  assert (x + y) == 10
  assert (x - y) == 11
  assert (x * y) == 12
  assert (x / y) == 13
  assert (x % y) == 14
  assert (x ** y) == 15
  assert (x // y) == 16

  assert (x << y) == 20
  assert (x >> y) == 21
  assert (x | y) == 22
  assert (x ^ y) == 23
  assert (x & y) == 24

def overload2():
  x = 1
  y = RightOver()
  assert (x == y) == 1
  assert (x != y) == 2
  assert (x <  y) == 3
  assert (x <= y) == 4
  assert (x >  y) == 5
  assert (x >= y) == 6

  assert (x + y) == 10
  assert (x - y) == 11
  assert (x * y) == 12
  assert (x / y) == 13
  assert (x % y) == 14
  assert (x ** y) == 15
  assert (x // y) == 16

  assert (x << y) == 20
  assert (x >> y) == 21
  assert (x | y) == 22
  assert (x ^ y) == 23
  assert (x & y) == 24

class Access:
  def __setitem__(self, x, y):
    self.val = y
  def __getitem__(self, x):
    return 77

def overload3():
  a = Access()
  a[1] = 2
  assert a.val == 2

def overload4():
  a = Access()
  assert a[1] == 77

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
  cls_fields1,
  cls_fields2,
  cls_methods,
  overload1,
  overload2,
  overload3,
  overload4,
  ])
def test_succeed(f):
  run_success(f, ())


# Boundary crossing
# Check objects that originate from Python

def cross1(a):
  assert a.x == 1
  assert a.y == None

# test each function in turn
@pytest.mark.parametrize("f", [
  cross1,
  ])
def test_crossing(f):
  a = A()
  a.x = 1
  a.y = None
  run_success(f, (a,))


# Failing cases
# (These functions are expected to fail elaboration to KLR)

def bad_init1():
  A(1,2,3)

def bad_attribute():
  a = A()
  a.unknown

def bad_cls_attribute():
  a.y

@pytest.mark.parametrize("f", [
  bad_init1,
  bad_attribute,
  bad_cls_attribute
])
def test_fails(f):
  run_fail(f, ())
