# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
import pytest
import neuronxcc.nki.typing as nt

from klr.frontend import Kernel

# Success cases
# (these functions should load and trace to KLR)

def expr_list(t):
  assert [1,2,False]
  assert not []

def modify():
  l = [1]
  x = l
  assert x == [1]
  l[0] = 5
  assert l[0] == 5
  assert l == [5]
  assert x == [5]

def append():
  l = []
  l.append(2)
  assert l[0] == 2
  l.append(5)
  assert l == [2,5]

def clear():
  l = [1,2,3]
  l.clear()
  assert l == []

def copy():
  l = [1,2,3]
  x = l
  y = l.copy()
  x[0] = 4
  assert l == [4,2,3]
  assert x == l
  assert y == [1,2,3]

def count():
  l = [1,(2,3),4]
  assert l.count() == 3
  l.clear()
  assert l.count() == 0
  assert [[2]].count() == 1

def extend():
  l = []
  l.extend((1,2,3))
  assert l == [1,2,3]
  l.extend([4])
  assert l == [1,2,3,4]

def index():
  l = [1,2,3]
  i = l.index(3)
  assert i == 2
  assert l.index(7) == None

def pop():
  l = [1,2,3]
  x = l.pop()
  assert x == 3
  assert l == [1,2]

def remove():
  l = [3,1,3,2,3,3]
  l.remove(3)
  assert l == [1,2]

def reverse():
  l = [1,2,4,3]
  l.reverse()
  assert l == [3,4,2,1]

# test each function in turn
@pytest.mark.parametrize("f", [
  expr_list,
  modify,
  append,
  clear,
  copy,
  count,
  extend,
  index,
  pop,
  remove,
  reverse,
  ])
def test_succeed(f):
  t = nt.tensor("float32", (10,10,10))
  F = Kernel(f)   # parse python
  F.specialize((t,))
  F.trace("tmp.klr")
  os.remove("tmp.klr")


# Failing cases
# (These functions are expected to fail elaboration to KLR)

def out_of_bounds():
  l = [1,2]
  l[3] = 0

@pytest.mark.parametrize("f", [
  out_of_bounds,
])
def test_fails(f):
  with pytest.raises(Exception):
    F = Kernel(f)
    F.specialize()
    F.trace("tmp.klr")
    os.remove("tmp.klr")
