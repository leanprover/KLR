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
  `(#eval IO.println (run $s "<input>"))

/--
info: ok:
foo : ∀ A. func[A, A]
-/
#guard_msgs in #type_check "
def foo[A](a : A) -> A:
  return a
"

/--
info: ok:
foo : ∀ A. func[A, A]
-/
#guard_msgs in #type_check "
def foo[A](a : A):
  return a
"

/--
info: ok: foo : ∀ A. func[A, A]
-/
#guard_msgs in #type_check "
def foo[A](a) -> A:
  return a
"

/--
info: ok: foo : ∀ 'T1. func['T1, 'T1]
-/
#guard_msgs in #type_check "
def foo(a):
  return a
"

/--
info: ok: matmul : func[tensor[int8, (10, 10)]]
-/
#guard_msgs in #type_check "
def matmul() -> tensor[int8, (10, 10)]:
  pass
"

/--
info: ok: matmul : ∀ DT M N K. func[tensor[DT, (M, N)], tensor[DT, (N, K)], tensor[DT, (M, K)]]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[DT, (M, N)], b : tensor[DT, (N, K)]) -> tensor[DT, (M, K)]:
  pass
"

/-- info:
ok: matmul : ∀ DT M N K. func[tensor[DT, (M, N)], tensor[DT, (N, K)], tensor[DT, (M, K)]]
apply_matmul : ∀ 'T5 'T6 'T7 'T8. func[tensor['T5, ('T6, 'T7)], tensor['T5, ('T7, 'T8)], tensor['T5, ('T6, 'T8)]]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[DT, (M, N)], b : tensor[DT, (N, K)]) -> tensor[DT, (M, K)]:
  pass

def apply_matmul(a, b):
  return matmul(a, b)
"

/--
info: ok: matmul : ∀ DT M N K. func[tensor[DT, (M, N)], tensor[DT, (N, K)], tensor[DT, (M, K)]]
apply_matmul : func[tensor[int, (10, 20)], tensor[int, (20, 30)], tensor[int, (10, 30)]]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[DT, (M, N)], b : tensor[DT, (N, K)]) -> tensor[DT, (M, K)]:
  pass

def apply_matmul(a : tensor[int, (10, 20)], b : tensor[int, (20, 30)]):
  return matmul[int, 10, 20, 30](a, b)
"

/--
info: ok: matmul : ∀ DT M N K. func[tensor[DT, (M, N)], tensor[DT, (N, K)], tensor[DT, (M, K)]]
apply_matmul : func[tensor[int, (10, 20)], tensor[int, (20, 30)], tensor[int, (10, 30)]]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[DT, (M, N)], b : tensor[DT, (N, K)]) -> tensor[DT, (M, K)]:
  pass

def apply_matmul(a : tensor[int, (10, 20)], b : tensor[int, (20, 30)]):
  return matmul(a, b)
"

/--
info: error: TypeError: <input>:5:62:
  def apply_matmul(a : tensor[int, (10, 20)], b : tensor[int, (25, 30)]):
                                                               ^^
expected size to be 20, got 25
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[DT, (M, N)], b : tensor[DT, (N, K)]) -> tensor[DT, (M, K)]:
  pass

def apply_matmul(a : tensor[int, (10, 20)], b : tensor[int, (25, 30)]):
  return matmul(a, b)
"

/--
info: ok: foo : func[float]
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
info: ok: ite : func[int]
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
ite : func[int]
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
higher : func[∀ DT M N. func[tensor[DT, (M, N)]], tensor[int, (10, 20)]]
-/
#guard_msgs in #type_check "
def higher(mk_tensor : forall[DT, M, N, func[tensor[DT, (M, N)]]]):
  m = mk_tensor[int, 10, 20]()
  return m
"

/--
info: ok:
higher : func[∀ DT M N. func[tensor[DT, (M, N)]], tensor[int, (10, 20)]]
-/
#guard_msgs in #type_check "
def higher(mk_tensor : forall[DT, M, N, func[tensor[DT, (M, N)]]]):
  m : tensor[int, (10, 20)] = mk_tensor()
  return m
"

/--
info: ok:
matmul : ∀ DT M N K. func[tensor[DT, (M, N)], tensor[DT, (N, K)], tensor[DT, (M, K)]]
higher : ∀ M N K. func[∀ DT M N. func[tensor[DT, (M, N)]], tensor[int, (M, K)]]
zeros : ∀ DT M N. func[tensor[DT, (M, N)]]
call_higher : func[tensor[int, (10, 30)]]
-/
#guard_msgs in #type_check "
def matmul[DT, M, N, K](a : tensor[DT, (M, N)], b : tensor[DT, (N, K)]) -> tensor[DT, (M, K)]:
  pass

def higher[M, N, K](mk_tensor : forall[DT, M, N, func[tensor[DT, (M, N)]]]):
  m : tensor[int, (M, N)] = mk_tensor()
  n : tensor[int, (N, K)] = mk_tensor()
  return matmul(m, n)

def zeros[DT, M, N]() -> tensor[DT, (M, N)]:
  pass

def call_higher():
  return higher[10, 20, 30](zeros)
"
