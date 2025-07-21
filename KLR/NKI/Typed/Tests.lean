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

import KLR.NKI.Typed.Grammar

open KLR.NKI.Typed
open DSL

def ret_none() -> None:
  return None

def ret_none_assign() -> None:
  return ret_none()

def ret_none_two_assign() -> None:
  x = 0
  y = x

def ret_none_three_assigns() -> None:
  x = 0
  y : int = x
  z = y

def nested[A]() -> A -> A:
  def id(a):
    return a
  return id

def nestedRec1[A]() -> A -> A:
  def id(a):
    return id(a)
  return id

def nestedRec2[A]() -> A -> A:
  def id(a):
    return nested[A](a)
  return id

def explode() -> int:
  return explode()

def foo(a : int) -> int:
  return a

def baz(a : int) -> int:
  def foo(a, _):
    return a
  return foo(a, a)

def call_foo() -> int:
  x = 0
  y = x
  z = y
  return foo(z)

def S[A, B, C](x : A -> B -> C, y : A -> B, z : A) -> C:
  return x(z, y(z))

def K[A, B](a : A, _ : B) -> A:
  return a

def I[A]() -> A -> A:
  return S[A, A -> A, A](K[A, A -> A](), K[A, A]())

def forty_two() -> int:
  return I[int](42)

def ite1(b : bool) -> int:
  b = False if b else True
  if b:
    return 0
  return 1

def ite_ret(a : int, b : bool) -> int:
  if b:
    return a
  else:
    return ite1(True)

def ite_cont(a : int, b : bool) -> int:
  if b:
    return a
  else:
    x = 0
  return 0

def whl() -> bool:
  while whl():
    x = 0
  return whl()

def for_() -> bool:
  for i in range(10):
    I[int](i)
  return whl()

def arith() -> None:
  x = 0 + 1
  y = x + 0 * x
  y = x + 0 - y
  z : float = y / 0.0 * 1
  z = z // 0.0 * 1.1
  z = y ** 0 * z
  z = z % 10 * 1

def booleans() -> None:
  x = True and False
  y = x or False and True
  0 < 1.1 and False
  x and 100 > 1
  y and 100 >= 1
  100.42 <= 1.1

def compares(a : int, b : int) -> bool:
  x = 0 == 0
  y = 1.2 != 0.1
  z = x == y
  return a == b and z

def poly_eq[A](x : A, y : A) -> bool:
  return x == y
