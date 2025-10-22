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
import Util.Float

/-
Python related builtins
-/

namespace KLR.Trace
open Core

/-
Constants for the global environment
-/
def pythonEnv : List (Name × Term) := [
  (`math.pi,  .float 3.141592653589793),
  (`math.e,   .float 2.718281828459045),
  (`math.inf, .float (1.0 / 0.0)),
  (`math.nan, .float (0.0 / 0.0)),
  ]

/-
The builtin.op namespace is used internally by the NKI compiler.
These functions are inserted in place of operators.
-/
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

/-
The builtin.python namespace is mapped to the top-level namespace.
For example, builtin.python.f will appear as f.
-/

nki builtin.python.isinstance (t : Term) (ty : Term) := do
  match t, ty with
  | .object cls .., .source { name, .. }
  | .ref _ (.object cls), .source { name, .. } => return .bool (cls == name)
  | .none, .builtin `builtin.python.NoneType ..
  | .bool .., .builtin `builtin.python.bool ..
  | .int .., .builtin `builtin.python.int ..
  | .float .., .builtin `builtin.python.float ..
  | .string .., .builtin `builtin.python.str ..
  | .tuple .., .builtin `builtin.python.tuple ..
  | .list .., .builtin `builtin.python.list ..
  | .ref _ .list, .builtin `builtin.python.list ..
  | .dict .., .builtin `builtin.python.dict ..
  | .ref _ .dict, .builtin `builtin.python.dict ..
  | .scalar .., .builtin `builtin.typing.scalar ..
  | .ellipsis, .builtin `builtin.python.ellipsis ..
  | .slice .., .builtin `builtin.python.slice .. => return .bool true
  | _, _ => return .bool false

nki builtin.python.NoneType := do
  return .none

nki builtin.python.EllipsisType := do
  return .ellipsis

nki builtin.python.ellipsis := do
  return .ellipsis

nki builtin.python.slice (args : List Term) := do
  match args with
  | [e]     => return .slice (some 0) (<- fromNKI? e) (some 1)
  | [b,e]   => return .slice (<- fromNKI? b) (<- fromNKI? e) (some 1)
  | [b,e,s] => return .slice (<- fromNKI? b) (<- fromNKI? e) (<- fromNKI? s)
  | _ => throw "invalid arguments"

nki builtin.python.print (args : List Term) := do
  let ts <- args.mapM Term.toStr
  message (" ".intercalate ts)
  return .none

-- TODO: DRY up the below code once we have more time
private def minTerms (a b : Term) : Trace Term := do
  match a, b with
  | .int a, .int b => return .int (min a b)
  | .float a, .float b => return .float (min a b)
  | .float a, .int b => return .float (min a b.toFloat64)
  | .int a, .float b => return .float (min a.toFloat64 b)
  | _, _ => throw "invalid arguments"

nki builtin.python.min (args : List Term) := do
  match args with
  | [] => throw "min expected at least 1 argument, got 0"
  | [.ref name .list] =>
    let arr <- match <- lookup name with
      | .list arr => pure arr
      | _ => throw "internal error: expecting list"
    if arr.isEmpty then throw "can't take min of empty sequence"
    arr.foldlM minTerms arr[0]!
  | [.tuple a]
  | [.list a] =>
    if a.isEmpty then throw "can't take min of empty sequence"
    a.foldlM minTerms a[0]!
  | [a, b] =>
    minTerms a b
  | _ => throw s!"invalid arguments {repr args}"

private def maxTerms (a b : Term) : Trace Term := do
  match a, b with
  | .int a, .int b => return .int (max a b)
  | .float a, .float b => return .float (max a b)
  | .float a, .int b => return .float (max a b.toFloat64)
  | .int a, .float b => return .float (max a.toFloat64 b)
  | _, _ => throw "invalid arguments"

nki builtin.python.max (args : List Term) := do
  match args with
  | [] => throw "max expected at least 1 argument, got 0"
  | [.ref name .list] =>
    let arr <- match <- lookup name with
      | .list arr => pure arr
      | _ => throw "internal error: expecting list"
    if arr.isEmpty then throw "can't take max of empty sequence"
    arr.foldlM maxTerms arr[0]!
  | [.tuple a]
  | [.list a] =>
    if a.isEmpty then throw "can't take max of empty sequence"
    let max := a[0]!
    a.foldlM maxTerms max
  | [a, b] =>
    maxTerms a b
  | _ => throw s!"invalid arguments {repr args}"

nki builtin.python.abs (t : Term) := do
  match t with
  | .bool true => return .int 1
  | .bool false => return .int 0
  | .int (.ofNat n) => return .int n
  | .int (.negSucc n) => return .int (n+1)
  | .float f => return .float f.abs
  | _ => throw "abs expects an integer or float number"

nki builtin.python.str (t : Term) := do
  return .string (<- t.toStr)

nki builtin.python.bool (t : Term) := do
 return .bool (<- t.isTrue)

nki builtin.python.int (t : Term) := do
  match t with
  | .none       => throw "None cannot be converted to an integer"
  | .bool true  => return .int 1
  | .bool false => return .int 0
  | .int i      => return .int i
  | .float f    =>
      -- Python is a bit strange here, it truncates both
      -- positive and negative numbers toward zero
      if f < 0.0 then
        return .int (Int.ofNat (Float.floor (-f)).toUInt64.toNat).neg
      else
        return .int (Int.ofNat (Float.floor f).toUInt64.toNat)
  | .string s   =>
      -- Fortunately, Lean's String.toInt appears to be compatible
      -- with Python's int(string) conversion.
      match s.toInt? with
      | .none  => throw s!"string {s} cannot be converted to an integer"
      | .some i => return .int i
  | _ => throw "value cannot be converted to an integer"

nki builtin.python.float (t : Term) := do
  match t with
  | .none       => throw "None cannot be converted to an number"
  | .bool true  => return .float 1.0
  | .bool false => return .float 0.0
  | .int i      => return .float (Float.ofInt i)
  | .float f    => return .float f
  | .string s   => return .float (KLR.Util.parseFloat s)
  | _ => throw "value cannot be converted to an number"

nki builtin.python.divmod (x : Int) (y : Int) := do
  return .tuple [ .int (x / y), .int (x % y) ]

/-
Python List object
-/

private def fetchIter (t : Term) : Trace (List Term) := do
  let t <- match t with
    | .ref name _ => lookup name
    | _ => pure t
  match t with
  | .none => return []
  | .tuple l => return l
  | .list a => return a.toList
  | _ => throw "not an iterable object"

private def fetchList (t : Term) : Trace (Name × Array Term) := do
  let name <- match t with
    | .ref name .list => pure name
    | _ => throw "expecting list reference"
  let arr <- match <- lookup name with
    | .list arr => pure arr
    | _ => throw "internal error: expecting list literal"
  return (name, arr)

private def modifyList (t : Term) (f : Array Term -> (Array Term × a)) : Trace a := do
  let (name, arr) <- fetchList t
  let (arr, x) := f arr
  extend_global name (.list arr)
  return x

nki builtin.python.tuple (t : Term) := do
  let l <- fetchIter t
  return .tuple l

nki builtin.python.list (t : Term) := do
  let name <- genName `list
  let l <- fetchIter t
  extend_global name (.list l.toArray)
  return .ref name .list

nki builtin.list.append (t : Term) (x : Term) := do
  modifyList t fun arr => (arr.push x, .none)

nki builtin.list.clear (t : Term) := do
  modifyList t fun _ => (#[], .none)

nki builtin.list.copy (t : Term) := do
  let (_, arr) <- fetchList t
  let name <- genName `list
  extend_global name (.list arr)
  return .ref name .list

nki builtin.list.count (t : Term) := do
  let (_, arr) <- fetchList t
  return .int arr.size

nki builtin.list.extend (t : Term) (x : Term) := do
  let l <- fetchIter x
  modifyList t fun arr => (arr.append l.toArray, .none)

-- Note: does not raise ValueError as in Python, simply returns none
nki builtin.list.index (t : Term) (value : Term) (start : Nat := 0) (stop : Nat := UInt64.size) := do
  let (_, arr) <- fetchList t
  match arr.findIdx? (. == value) with
  | none => return .none
  | some n => if n >= start && n < stop then return .int n else return .none

-- Note: like above no exceptions
nki builtin.list.pop (t : Term) := do
  modifyList t fun arr =>
    let x := arr[arr.size - 1]!
    (arr.pop, x)

-- Note: like above no exceptions
nki builtin.list.remove (t : Term) (v : Term) := do
  modifyList t fun arr => (arr.filter fun x => x != v, .none)

nki builtin.list.reverse (t : Term) := do
  modifyList t fun arr => (arr.reverse, .none)

/-
Python dict object
-/

private def fetchDict (t : Term) : Trace (Name × AA) := do
  let name <- match t with
    | .ref name .dict => pure name
    | _ => throw "expecting dictionary reference"
  let arr <- match <- lookup name with
    | .dict arr => pure arr
    | _ => throw "internal error: expecting dict literal"
  return (name, arr)

private def modifyDict (t : Term) (f : AA -> (AA × a)) : Trace a := do
  let (name, arr) <- fetchDict t
  let (arr, x) := f arr
  extend_global name (.dict arr)
  return x

nki builtin.python.dict (t : List (String × Term) := []) := do
  let name <- genName `dict
  extend_global name (.dict t.toArray)
  return .ref name .dict

nki builtin.dict.clear (t : Term) := do
  modifyDict t fun _ => (#[], .none)

nki builtin.dict.copy (t : Term) := do
  let (_, arr) <- fetchDict t
  let name <- genName `dict
  extend_global name (.dict arr)
  return .ref name .dict

nki builtin.dict.get (t : Term) (key : String) (dflt : Term := .none) := do
  let (_, arr) <- fetchDict t
  match arr.lookup? key with
  | some t => return t
  | none => return dflt

nki builtin.dict.items (t : Term) := do
  let (_, arr) <- fetchDict t
  return .list $ arr.map fun (s, t) => .tuple [.string s, t]

nki builtin.dict.keys (t : Term) := do
  let (_, arr) <- fetchDict t
  return .list $ arr.map fun (s, _) => .string s

nki builtin.dict.values (t : Term) := do
  let (_, arr) <- fetchDict t
  return .list $ arr.map fun (_, t) => t

nki builtin.dict.pop (t : Term) (key : String) (dflt : Term := .none) := do
  modifyDict t fun arr =>
    let (vs, arr) := arr.partition fun i => i.fst == key
    if h:vs.size > 0
    then (arr, (vs[0]'h).snd)
    else (arr, dflt)

nki builtin.dict.setdefault (t : Term) (key : String) (default : Term := .none) := do
  modifyDict t fun arr =>
    match arr.findIdx? fun item => item.fst = key with
    | none => (arr.push (key, default), default)
    | some i => (arr, (arr[i]!).snd)

/-
Utilities common to lists and dicts
-/
nki builtin.python.len (t : Term) := do
  try
    let l <- fetchIter t
    return .int l.length
  catch
    | _ =>
      try
        let d <- fetchDict t
        return .int d.snd.size
      catch
        | _ => throw s!"expected a list of a dictionary; found {Term.kindStr t}"


/-
Python math library
-/

nki math.ceil (x : Float) := do
  return .int x.ceil.toInt

nki math.floor (x : Float) := do
  return .int x.floor.toInt

nki math.gcd (x : Int) (y : Int) := do
  return .int (Int.ofNat $ Int.gcd x y)

nki math.log2 (x : Float) := do
  return .float x.log2

nki math.log10 (x : Float) := do
  return .float x.log10

nki math.pow (x : Float) (y : Float) := do
  return .float (x ^ y)

nki math.sqrt (x : Float) := do
  return .float x.sqrt
