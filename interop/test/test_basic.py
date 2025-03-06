# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
from apis import *

# this needs to be after the apis
import numpy as np
import pytest

from klr import Kernel

# Success cases
# (these functions should load and trace to KLR)

def const_stmt(t):
  "this will be ignored because it has no effect"
  1     # so will this, it is a simple constant
  1.0   # so will this
  False # and this
  None  # and this
  (1,2) # and this
  [1,2] # and this

string = "a string"
integer = -3
floating = 1.23
boolean = True
nothing = None
triple = (1, floating, False)
list3 = [string, triple, np]

def expr_name(t):
  # these names will end up in the global environment after parsing
  # they will be eliminated after substitution during tracing
  string, integer, floating, boolean, nothing
  # constant tuples are also OK
  triple
  # as are constant lists
  list3
  # as are module references
  np

def expr_tuple(t):
  assert (1,False,"hello")

def expr_list(t):
  assert [1,2,False]
  assert not []

def expr_subscript(t):
  t[1]
  t[1,2]
  t[1:2:3]
  t[1:2]
  t[1:]
  t[1::]
  t[1::2]
  t[1:2:None]
  t[1:None:2]
  t[:]
  t[:,:]
  t[:,:,:]
  t[...]
  t[1,...]
  t[...,1]
  t[:,None]
  t[1]

def expr_bool_op(t):
  True and 1 and [1] and [] and True  # evals to []
  False or None or [] or 1 # evals to 1
  1 or None  # evals to 1
  (False,) or 1  # evals to (False,)

def expr_cmp_op(t):
  assert 1 == 1
  assert [] == []
  assert not ([1,2] == [1])
  assert not ([] < [])
  assert [] < [1]
  assert not ([1,2] < [1,2])
  assert [1,1] < [1,2]
  assert [1,2] < [1,2,3]
  assert 1.2 < 2
  assert 1 < 1.2
  assert 1.2 < 1.3
  assert 0.5 < True
  assert not (0.5 < False)
  assert "a" < "ab"
  assert (1,2) is (1,2)
  assert not ([1,2] is [1,2])
  assert 1 in (1,2)
  assert 1 in [3,2,1]
  assert 1 not in (2,3,4)
  assert 1 not in []

def assign(t):
  x = y = 1
  assert x == y
  x, y = [1,2]
  assert x == 1
  assert y == 2
  (x,y), z = a, [b,c] = ((1,2),(3,4))
  assert x == 1
  assert y == 2
  assert z == (3,4)
  assert a == (1,2)
  assert b == 3
  assert c == 4

def ifs(t):
  x = 0
  if x: x = 1
  else: x = 2
  assert x == 2
  if x: x = 1
  else: x = 2
  assert x == 1

def loops(t):
  for x in [1,2,3,4]:
    if x == 1: continue
    assert x != 1
    if x == 3: break
  assert x == 3

# some undefined names are OK
def undefined_ok(t):
  nl.foo(t)

# test each function in turn
@pytest.mark.parametrize("f", [
  const_stmt,
  expr_name,
  expr_tuple,
  expr_list,
  expr_subscript,
  expr_bool_op,
  expr_cmp_op,
  assign,
  ifs,
  loops,
  undefined_ok
  ])
def test_succeed(f):
  t = np.ndarray((10,10,10), dtype="float32")
  F = Kernel(f)   # parse python
  file = F(t)     # specialize, and reduce to KLR
  os.remove(file)

# Failing cases
# (These functions are expected to fail elaboration to KLR)

def name_not_found():
  x

@pytest.mark.parametrize("f", [
  name_not_found,
])
def test_fails(f):
  F = Kernel(f)
  with pytest.raises(Exception):
    F()

if __name__ == '__main__':
  F = Parser(name_not_found)
  print(F())
