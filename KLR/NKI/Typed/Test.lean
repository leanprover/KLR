/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import KLR.NKI.Typed.Elab

namespace KLR.NKI.Typed.Test

macro "#type_check " s:str : command =>
  `(#eval IO.println (runTypechecker $s "<input>"))

/--
info: ok:
foo : forall A. [A] -> A
-/
#guard_msgs in #type_check "
def foo[A](a : A) -> A:
  return a
"

/--
info: ok:
foo : forall A. [A] -> A
-/
#guard_msgs in #type_check "
def foo[A](a : A):
  return a
"

/--
info: ok:
foo : forall A. [A] -> A
-/
#guard_msgs in #type_check "
def foo[A](a) -> A:
  return a
"

/--
info: ok:
foo : forall 'T1. ['T1] -> 'T1
-/
#guard_msgs in #type_check "
def foo(a):
  return a
"

/--
info: ok:
matmul : [] -> tensor[(10, 10), int8]
-/
#guard_msgs in #type_check "
def matmul() -> tensor[(10, 10), int8]:
  pass
"

/--
info: ok:
matmul : forall DT M N K. [tensor[(M, N), DT], tensor[(N, K), DT]] -> tensor[(M, K), DT]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[(M, N), DT], b : tensor[(N, K), DT]) -> tensor[(M, K), DT]:
  pass
"

/--
info: ok:
matmul : forall DT M N K. [tensor[(M, N), DT], tensor[(N, K), DT]] -> tensor[(M, K), DT]
apply_matmul : forall 'T5 'T6 'T7 'T8. [tensor[('T6, 'T7), 'T5], tensor[('T7, 'T8), 'T5]] -> tensor[('T6, 'T8), 'T5]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[(M, N), DT], b : tensor[(N, K), DT]) -> tensor[(M, K), DT]:
  pass

def apply_matmul(a, b):
  return matmul(a, b)
"

/--
info: ok:
matmul : forall DT M N K. [tensor[(M, N), DT], tensor[(N, K), DT]] -> tensor[(M, K), DT]
apply_matmul : [tensor[(10, 20), int], tensor[(20, 30), int]] -> tensor[(10, 30), int]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[(M, N), DT], b : tensor[(N, K), DT]) -> tensor[(M, K), DT]:
  pass

def apply_matmul(a : tensor[(10, 20), int], b : tensor[(20, 30), int]):
  return matmul[int, 10, 20, 30](a, b)
"

/--
info: ok:
matmul : forall DT M N K. [tensor[(M, N), DT], tensor[(N, K), DT]] -> tensor[(M, K), DT]
apply_matmul : [tensor[(10, 20), int], tensor[(20, 30), int]] -> tensor[(10, 30), int]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[(M, N), DT], b : tensor[(N, K), DT]) -> tensor[(M, K), DT]:
  pass

def apply_matmul(a : tensor[(10, 20), int], b : tensor[(20, 30), int]):
  return matmul(a, b)
"

/--
info: error:
TypeError: <input>:5:57:
  def apply_matmul(a : tensor[(10, 20), int], b : tensor[(25, 30), int]):
                                                          ^^
expected size to be 20, got 25
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[(M, N), DT], b : tensor[(N, K), DT]) -> tensor[(M, K), DT]:
  pass

def apply_matmul(a : tensor[(10, 20), int], b : tensor[(25, 30), int]):
  return matmul(a, b)
"

/--
info: ok:
foo : [] -> float
-/
#guard_msgs in #type_check "
def foo():
  return 0 if True else 1.
"

/--
info: error: TypeError: <input>:7:5:
      a = 1
      ^
expected int, got None
-/
#guard_msgs in #type_check "
def ite():
  a = 0
  if True:
    return 0
  else:
    a = 1
"

/--
info: ok:
ite : [] -> int
-/
#guard_msgs in #type_check "
def ite():
  a = 0
  if True:
    return 0
  else:
    return a
"

/--
info: ok:
ite : [] -> int
-/
#guard_msgs in #type_check "
def ite():
  a = 0
  if True:
    return 0
  else:
    a = 1
  return a
"

/--
info: ok:
higher : [forall DT M N. [] -> tensor[(M, N), DT]] -> tensor[(10, 20), int]
-/
#guard_msgs in #type_check "
def higher(mk_tensor : forall DT M N. [] -> tensor[(M, N), DT]):
  m = mk_tensor[int, 10, 20]()
  return m
"

/--
info: ok:
higher : [forall DT M N. [] -> tensor[(M, N), DT]] -> tensor[(10, 20), int]
-/
#guard_msgs in #type_check "
def higher(mk_tensor : forall DT M N. [] -> tensor[(M, N), DT]):
  m : tensor[(10, 20), int] = mk_tensor()
  return m
"

/--
info: ok:
matmul : forall DT M N K. [tensor[(M, N), DT], tensor[(N, K), DT]] -> tensor[(M, K), DT]
higher : forall M N K. [forall DT M N. [] -> tensor[(M, N), DT]] -> tensor[(M, K), int]
zeros : forall DT M N. [] -> tensor[(M, N), DT]
call_higher : [] -> tensor[(10, 30), int]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[(M, N), DT], b : tensor[(N, K), DT]) -> tensor[(M, K), DT]:
  pass

def higher[M, N, K](mk_tensor : forall DT M N. [] -> tensor[(M, N), DT]):
  m : tensor[(M, N), int] = mk_tensor()
  n : tensor[(N, K), int] = mk_tensor()
  return matmul(m, n)

def zeros[DT, M, N]() -> tensor[(M, N), DT]:
  pass

def call_higher():
  return higher[10, 20, 30](zeros)
"

/--
info: error:
TypeError: <input>:3:34:
  def foo[DT, M, N](a : tensor[DT, (M, N)]):
                                   ^^^^^^
kind mismatch, expected type, got shape. Did you mixed up the order of tensor shape and dtype?
-/
#guard_msgs in #type_check "

def foo[DT, M, N](a : tensor[DT, (M, N)]):
  pass

"

/--
info: ok:
foo : forall DT M N. [tensor[(M, N), DT]] -> tensor[(M, N), DT] where M <= 128, 32 | N
zeros : forall DT M N. [] -> tensor[(M, N), DT]
bar : [] -> tensor[(128, 128), int]
-/
#guard_msgs in #type_check "

def foo[DT, M, N](a : tensor[(M, N), DT])
where
  M <= 128
  32 | N
:
  return a

def zeros[DT, M, N]() -> tensor[(M, N), DT]:
  pass

def bar():
  a : tensor[(128, 128), int] = zeros()
  a = foo(a)
  return a

"

/--
info: error:
TypeError: <input>:14:15:
    a : tensor[(129, 128), int] = zeros()
                ^^^
size here must be less-than-equal-to 128
-/
#guard_msgs in #type_check "

def foo[DT, M, N](a : tensor[(M, N), DT])
where
  M <= 128
  32 | N
:
  return a

def zeros[DT, M, N]() -> tensor[(M, N), DT]:
  pass

def bar():
  a : tensor[(129, 128), int] = zeros()
  a = foo(a)
  return a

"

/--
info: error:
TypeError: <input>:14:20:
    a : tensor[(128, 129), int] = zeros()
                     ^^^
size here must be divisible by 32
-/
#guard_msgs in #type_check "

def foo[DT, M, N](a : tensor[(M, N), DT])
where
  M <= 128
  32 | N
:
  return a

def zeros[DT, M, N]() -> tensor[(M, N), DT]:
  pass

def bar():
  a : tensor[(128, 129), int] = zeros()
  a = foo(a)
  return a

"

/--
info: ok:
range : [int] -> iter[int]
forLoop : [int] -> int
-/
#guard_msgs in #type_check "

def range(n : int) -> iter[int]:
  pass

def forLoop(n : int):
  x = 0
  for i in range(n):
    x += i
  return x
"

/--
info: ok:
whileLoop : [] -> int
-/
#guard_msgs in #type_check "

def whileLoop():
  x = 0
  sum = 1
  while x < 10:
    sum *= x
    x += 1
  return x
"

/--
info: error:
TypeError: <input>:10:10:
    return y
           ^
variable not in scope
-/
#guard_msgs in #type_check "

def scoping(z):
  x = 0
  sum = 1
  for i in z:
    y = 0
    sum *= x
    x += 1
  return y
"

/--
info: ok:
example : [bool, int, int] -> int
-/
#guard_msgs in #type_check "

def example(a, b, c):
  if a:
    return b + 1
  else:
    return c

"
