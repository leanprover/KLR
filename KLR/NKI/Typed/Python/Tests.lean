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

-- import KLR.NKI.Typed.Parser
-- import Qq

-- namespace KLR.NKI.Typed.Tests
-- open KLR NKI Typed DSL

/-!
# Snapshot Testing for the Python Parser

TODO:
  Some of these outputs are very long so I haven't examined them closely.
  We should pretty-print `PIR.Prog` instead of showing the raw Lean data structures
  so that auditing the output is manageable.
-/

-- open Qq in
-- elab "nki[" prog:str "]" : term => do
--   let prog ← expandPythonFromString "<input>" prog.getString
--   Lean.Elab.Term.elabTerm prog q(PIR.Prog)

-- #check nki["

-- def ret_none(_):
--   return None

-- "]

-- #check nki["

-- # asdf
-- def str(): #comment
-- #comment
--   return \"#as#df\" #com
-- #comment
-- "]

-- #check nki["

-- def ret_none(t : tuple[int, float, bool]):
--   return None

-- "]

-- #check nki["

-- def bar(a, b:int=0, c=10):
--   print[A, b](\"bar called\", a=0)

-- "
-- ]

-- #check nki["

-- def foo():
--   return 0 + 1

-- "]

-- #check nki["

-- def access():
--   b = a[0]
--   b = a[...]
--   b = a[:]
--   b = a[0:]
--   b = a[:1]
--   b = a[0:1]
--   b = a[::]
--   b = a[: :]
--   b = a[0::]
--   b = a[0: :]
--   b = a[:1:]
--   b = a[::2]
--   b = a[: :2]
--   b = a[0:1:]
--   b = a[0::2]
--   b = a[0: :2]
--   b = a[:1:2]
--   b = a[0:1:2]
--   b = a[:, ..., ::, ..., 0]

-- "]

-- #check nki["

-- def tuples(t : tuple[int]) -> int:
--   _ = t
--   a, = t
--   return a

-- def comprehensive_tuple_tests():
--   (a, b), (c, d) = ((0, 1), (True, False))
--   x, y = 1, 2
--   (p, q) = 3, 4
--   foo()
--   (m, n), o = (5, 6), 7
--   foo()
--   single, = (42,)
--   first, second, third = 10, 20, 30
--   ((nested1, nested2), flat) = ((100, 200), 300)
--   simple = 999
--   result = (a + b, c + d)

--   w, (x, y), z = 1, (2, 3), 4
--   ((a, b), c), (d, (e, f)) = ((10, 20), 30), (40, (50, 60))

--   _ = (1, 2, 3)
--   _, middle, _ = 7, 8, 9

--   if c:
--     return a
--   elif c:
--     return b
--   else:
--     return a + b

-- "]
