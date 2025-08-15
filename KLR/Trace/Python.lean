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

import KLR.Core
import KLR.Trace.ISA
import KLR.Trace.Types

/-
Python related builtins
-/

namespace KLR.Trace
open Core

nki builtin.op.negate (t : Term) := do
  match t with
  | (x : Int) => return x.neg
  | (x : Float) => return x.neg
  | _ => throw "cannot negate values of this type"

nki builtin.op.not (t : Term) := do
  t.isFalse

nki builtin.op.invert (t : Term) := do
  let i : Int <- fromNKI? t
  return i.toInt32.complement.toInt

nki builtin.python.slice (b : Int) (e : Int) (s : Int) := do
  return .slice b e s

nki builtin.python.len (t : Term) := do
  match t with
  | .tuple l | .list l => return .expr (.value (.int l.length)) .int
  | _ => throw "invalid argument"

-- TODO: should take arbitrary number of arguments and work on more types
nki builtin.python.min (a : Term) (b : Term) := do
  match a, b with
  | .expr (.value (.int a)) _, .expr (.value (.int b)) _ =>
     return .expr (.value (.int (min a b))) .int
  | _, _ => throw "invalid arguments"


/-
Python math library
-/

nki math.gcd (a : Term) (b : Term) := do
  match a, b with
  | (x : Int), (y : Int) => return Int.ofNat (Int.gcd x y)
  | _, _ => throw "gcd not avaliable for these types"
