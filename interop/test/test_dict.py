# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
import pytest
from runner import *

from klr.frontend import Kernel

# Success cases
# (these functions should load and trace to KLR)

def expr_dict():
  assert {'a':1}
  assert dict()
  assert dict([('a', 1), ('b', 2)])

def modify():
  d = {'a':1}
  assert d['a'] == 1
  d['a'] = 2
  assert d['a'] == 2
  d['b'] = 7
  assert d['b'] == 7
  assert d == {'a':2, 'b':7}

def clear():
  d = {'a':1}
  d.clear()
  assert d == dict()

def copy():
  d = {'a':1}
  d2 = d.copy()
  d['b'] = 4
  assert d == {'a':1, 'b':4}
  assert d2 == {'a':1}

def get():
  d = dict()
  d['a'] = 1
  assert d.get('a') == 1
  assert d.get('a', 5) == 1
  assert d.get('b') == None
  assert d.get('b', 5) == 5

def items():
  d = {'a':1, 'b':2}
  assert d.items() == [ ('a', 1), ('b', 2) ]

def keys():
  d = {'a':1, 'b':2}
  assert d.keys() == ['a','b']

def pop():
  d = {'a':1, 'b':2}
  x = d.pop('a')
  assert x == 1
  assert d == {'b':2}
  x = d.pop('c', 5)
  assert x == 5
  assert d == {'b':2}
  x = d.pop('c')
  assert x == None
  assert d == {'b':2}

def setdefault():
  d = dict([('a', 1)])
  x = d.setdefault('b', 2)
  assert x == 2
  assert d == {'a':1, 'b':2}
  x = d.setdefault('a', 2)
  assert x == 1
  assert d == {'a':1, 'b':2}

def values():
  d = {'a':1, 'b':2}
  assert d.values() == [1, 2]

def dict_len():
  assert len({}) == 0
  assert len({'a':1, 'b':2}) == 2
  d1 = {}
  assert len(d1) == 0
  d2 = {'a':1, 'b':2}
  assert len(d2) == 2
  d2.pop('c')
  assert len(d2) == 2
  d2.pop('a')
  assert len(d2) == 1
  d2.pop('b')
  assert len(d2) == 0

# test each function in turn
@pytest.mark.parametrize("f", [
  expr_dict,
  modify,
  clear,
  copy,
  get,
  items,
  keys,
  pop,
  setdefault,
  values,
  dict_len,
  ])
def test_succeed(f):
  run_success(f, ())

# Failing cases
# (These functions are expected to fail elaboration to KLR)

def out_of_bounds():
  l = [1,2]
  l[3] = 0

@pytest.mark.parametrize("f", [
  out_of_bounds,
])
def test_fails(f):
  run_fail(f, ())
