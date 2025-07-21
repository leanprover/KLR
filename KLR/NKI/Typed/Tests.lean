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

def ret_none() -> none:
  return None

def ret_none_assign() -> none:
  return ret_none()

def ret_none_two_assign() -> none:
  x = 0
  y = x

def ret_none_three_assigns() -> none:
  x = 0
  y : int = x
  z = y

def nested[A]() -> A -> A:
  def id(a):
    return (a)
  return id

def_rec explode() -> int:
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

def foo2(b : bool) -> int:
  b = False if b else True
  if b:
    return 0
  return 1

def bar(a : int, b : bool) -> int:
  if b:
    return a
  else:
    return foo2(True)
