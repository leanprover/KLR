# This file exercises the Lean partial evaluator with
# a set of basic unit tests. Each function is parsed,
# handed to Lean, where it is checked and reduced to KLR.

import os
import pytest
import neuronxcc.nki.typing as nt

from klr.frontend import Kernel

# Success cases
# (these functions should load and trace to KLR)

class A:
  x : int = 1
  y : bool = True

def fstr1():
  assert f"hello" == "hello"

def fstr2():
  a = A()
  assert f"{a}" == "A(x:1,y:True)"

def fstr3():
  assert f"{1} {1+2} {'a'}" == "1 3 a"

def fstr4():
  assert f"{[1,2,3]}" == "[1,2,3]"

def fstr5():
  assert f"{(1,2,3)}" == "(1,2,3)"

def fstr6():
  x = {'a':1,'b':2}
  assert f"{x}" == "{a:1,b:2}"

# test each function in turn
@pytest.mark.parametrize("f", [
  fstr1,
  fstr2,
  fstr3,
  fstr4,
  fstr5,
  fstr6,
  ])
def test_succeed(f):
  t = nt.tensor("float32", (10,10,10))
  F = Kernel(f)   # parse python
  F.specialize()
  F.trace("tmp.klr")
  os.remove("tmp.klr")
