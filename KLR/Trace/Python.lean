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
  | .int x => return .int x.neg
  | .float x => return .float x.neg
  | _ => throw "cannot negate values of this type"

nki builtin.op.not (t : Term) := do
  return .bool (<- t.isFalse)

nki builtin.op.invert (t : Term) := do
  let i : Int <- fromNKI? t
  return .int i.toInt32.complement.toInt

nki builtin.python.slice (b : Int) (e : Int) (s : Int) := do
  return .slice b e s

private partial def termStr : Term -> Trace String
  | .module name => return name.toString
  | .builtin name _ => return name.toString
  | .ref name _ => do termStr (<- lookup name)
  | .source f => return f.name
  | .var name => do termStr (<- lookup name)
  | .none => return "None"
  | .bool true => return "True"
  | .bool false => return "False"
  | .int i => return toString i
  | .float f => return toString f
  | .string s => return s
  | .access .. => return "<Access>"
  | .tuple ts => return "("++ ",".intercalate (<- ts.mapM termStr) ++")"
  | .list ts => return "["++ ",".intercalate (<- ts.toList.mapM termStr) ++"]"
  | .ellipsis => return "..."
  | .slice .. => return "<slice>"
  | .pointer .. => return "<ptr>"
  | .mgrid => return "<mgrid>"
  | .mgItem .. => return "<mgrid_item>"

nki builtin.python.print (t : Term) := do
  message (<- termStr t)
  return .none

nki builtin.python.len (t : Term) := do
  match t with
  | .tuple l => return .int l.length
  | .list a => return .int a.size
  | _ => throw "invalid argument"

-- TODO: should take arbitrary number of arguments and work on more types
nki builtin.python.min (a : Term) (b : Term) := do
  match a, b with
  | .int a, .int b => return .int (min a b)
  | _, _ => throw "invalid arguments"

/-
Python List object
-/

private def fetchIter (t : Term) : Trace (List Term) := do
  let t <- match t with
    | .ref name _ => lookup name
    | _ => pure t
  match t with
  | .tuple l => return l
  | .list a => return a.toList
  | _ => throw "not an iterable object"

private def fetchList (t : Term) : Trace (Name × Array Term) := do
  let name <- match t with
    | .ref name .list => pure name
    | _ => throw "internal error: expecting list reference"
  let arr <- match <- lookup name with
    | .list arr => pure arr
    | _ => throw "internal error: expecting reference to list"
  return (name, arr)

private def modifyList (t : Term) (f : Array Term -> Array Term) : Trace Unit := do
  let (name, arr) <- fetchList t
  extend name (.list (f arr))

nki builtin.list.append (t : Term) (x : Term) := do
  modifyList t fun arr => arr.push x
  return .none

nki builtin.list.clear (t : Term) := do
  modifyList t fun _ => #[]
  return .none

nki builtin.list.copy (t : Term) := do
  let (_, arr) <- fetchList t
  let name <- genName `list
  extend name (.list arr)
  return .ref name .list

nki builtin.list.count (t : Term) := do
  let (_, arr) <- fetchList t
  return .int arr.size

nki builtin.list.extend (t : Term) (x : Term) := do
  let l <- fetchIter x
  modifyList t fun arr =>
    arr.append l.toArray
  return .none

-- Note: does not raise ValueError as in Python, simply returns none
nki builtin.list.index (t : Term) (value : Term) (start : Nat := 0) (stop : Nat := UInt64.size) := do
  let (_, arr) <- fetchList t
  match arr.findIdx? (. == value) with
  | none => return .none
  | some n => if n >= start && n < stop then return .int n else return .none

-- Note: like above no exceptions
nki builtin.list.pop (t : Term) := do
  let (name, arr) <- fetchList t
  let x := arr[arr.size - 1]!
  extend name (.list arr.pop)
  return x

-- Note: like above no exceptions
nki builtin.list.remove (t : Term) (v : Term) := do
  modifyList t fun arr =>
    arr.filter fun x => x != v
  return .none

nki builtin.list.reverse (t : Term) := do
  modifyList t fun arr =>
    arr.reverse
  return .none

/-
Python math library
-/

nki math.gcd (a : Term) (b : Term) := do
  match a, b with
  | .int x, .int y => return .int (Int.ofNat $ Int.gcd x y)
  | _, _ => throw "gcd not avaliable for these types"
