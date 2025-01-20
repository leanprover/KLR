import numpy as np
import nki
import pytest

from nkl.parser import Parser

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
list3 = [string, triple, nki]

def expr_name(t):
  # these names will end up in the global environment after parsing
  # they will be eliminated after substitution during tracing
  string, integer, floating, boolean, nothing
  # constant tuples are also OK
  triple
  # as are constant lists
  list3
  # as are module references
  nki

def expr_tuple(t):
  assert (1,False,"hello")

def expr_list(t):
  assert [1,2,nki]
  assert not []

def expr_subscript(t):
  t[1]
  t[1,2,3]
  t[1:2:3]
  t[1:2]
  t[1:]
  t[1::]
  t[1::2]
  t[1:2:None]
  t[1:None:2]
  t[:]
  t[:,:]
  t[...]
  t[1,...]
  t[:,None]
  t[1]

def expr_bool_op(t):
  True and 1 and [1] and [] and True  # evals to []
  False or None or [] or 1 # evals to 1
  1 or None  # evals to 1
  (False,) or 1  # evals to (False,)

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

@pytest.mark.parametrize("f", [
  const_stmt,
  expr_name,
  expr_tuple,
  expr_list,
  expr_subscript,
  expr_bool_op,
  assign
  ])
def test_succeed(f):
  t = np.ndarray(10)
  F = Parser(f)
  F(t)

# Failing cases
# (These functions are expected to fail elaboration to KLR)

def name_not_found():
  return x

@pytest.mark.parametrize("f", [
  name_not_found,
  ])
def test_fails(f):
  F = Parser(f)
  with pytest.raises(Exception):
    F()
