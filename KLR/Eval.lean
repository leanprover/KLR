/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import TensorLib
import TensorLib.Common
import TensorLib.Iterator
import TensorLib.Ufunc

open Lean(AssocList)
open StateT(lift)
open TensorLib(Iterator Tensor)
open TensorLib.Iterator(IntIter LEList)
open KLR.Core(AccessPattern Address AluOp APPair Operator Shape TensorName TensorScalar)

namespace KLR
namespace Eval

inductive EValue where
| EAccess (t : Core.Access)
| EBool (b : Bool)
| EFloat (n : Float)
| EInt (n : Int)
| ETensor (t : Tensor)

structure Env where
  env : List (String × EValue)

namespace Env

def lookup (env : Env) (x : String) : Option EValue := match env.env with
| [] => .none
| (x', t) :: env => if x == x' then some t else env.lookup x

def lookupTensor (env : Env) (t : String) : Err Tensor := match env.lookup t with
  | some (.ETensor t) => .ok t
  | some _ => throw s!"{t} is not a tensor in the current environment"
  | none => throw s!"{t} is not unbound in the current environment"

def insert (env : Env) (x : String) (v : EValue) : Env := Env.mk ((x, v) :: env.env)

end Env

abbrev WithEnv := StateT Env Err

def lookup (x : String) : WithEnv (Option EValue) := do
  let env <- get
  return env.lookup x

def lookupTensor (t : String) : WithEnv Tensor := do (<- get).lookupTensor t

def insertTensor (x : String) (t : Tensor) : WithEnv Unit := do
  modifyGet fun env => ((), env.insert x (.ETensor t))

-- def pure (x : a) : WithEnv a := StateT.pure x

-- def lift (x : Err a) : WithEnv a := StateT.lift x

private def evalDtype (dtype : KLR.Core.Dtype) : Err TensorLib.Dtype := match dtype with
| .int8 => .ok TensorLib.Dtype.int8
| .int16 => .ok TensorLib.Dtype.int16
| .int32 => .ok TensorLib.Dtype.int32
| .int64 => .ok TensorLib.Dtype.int64
| .uint8 => .ok TensorLib.Dtype.uint8
| .uint16 => .ok TensorLib.Dtype.uint16
| .uint32 => .ok TensorLib.Dtype.uint32
| .uint64 => .ok TensorLib.Dtype.uint64
| .float32 => .ok TensorLib.Dtype.float32
| .bfloat16
| .float8e3
| .float8e4
| .float8e5
| .float16
| .float32r => throw "Unsupported"

private def evalShape (shape : Shape) : TensorLib.Shape := TensorLib.Shape.mk shape.toList

private def checkIOTensor (name : TensorName) (t : Tensor) : Err Unit := do
  let dtype <- evalDtype name.dtype
  if dtype != t.dtype then throw s!"{name.name}: dtype mismatch" else
  if evalShape name.shape != t.shape then throw s!"{name.name}: shape mismatch"
  .ok ()

private def checkInputTensors (kernel : Core.Kernel) (inputs : List Tensor) : Err Unit :=
  let ins := kernel.inputs
  if ins.length != inputs.length then throw "Input length mismatch" else
  (ins.zip inputs).forA fun (name, t) => checkIOTensor name t

private def checkOutputTensors (kernel : Core.Kernel) : WithEnv Unit := do
  let outs := kernel.outputs
  for out in outs do
    match <- lookup out.name with
    | some (.ETensor t) => checkIOTensor out t
    | some _ => throw s!"Wrong type mapping for {out.name}"
    | none => throw s!"Missing mapping for {out.name}"

-- This differs from IntIter because step can be 0. We don't have a stop, but instead
-- have a count
structure APPairIter where
  private mk::
  pair : APPair
  start : Int
  current : Int
  remaining : Nat
  wf : remaining <= pair.num

namespace APPairIter

/-
`start` can be determined by the `offset` of an address
It may seem weird to start `remaining` as `pair.num - 1` rather than `pair.num`.
The reason is that we can already `peek` at the first value, so there are only
`num-1` more steps to do. This still works for `num = 0` since while you can
`peek` at the last/only element of the list, `next` and `size` will both be 0
so iteration will produce an empty list.

Incidentally, this is exactly the downside of making `peek` return a non-Option.
-/
def make (pair : APPair) (start : Int) : APPairIter :=
  APPairIter.mk pair start start (pair.num-1) (by simp)

instance iteratorInstance : Iterator APPairIter Int where
  next iter :=
    if iter.remaining == 0 then none else
    let current := iter.current + iter.pair.step
    let remaining := iter.remaining - 1
    let wf : remaining <= iter.pair.num := by let H := iter.wf; omega
    some { iter with current, remaining, wf }
  size iter := iter.pair.num
  peek iter := iter.current
  reset iter :=
    let current := iter.start
    let remaining := iter.pair.num-1
    let wf : remaining <= iter.pair.num := by omega
    { iter with current, remaining, wf }

#guard Iterator.toList (APPairIter.make (APPair.mk 1 5) 0) == [(0:Int), 1, 2, 3, 4]
#guard Iterator.toList (APPairIter.make (APPair.mk 1 5) 0) == [(0:Int), 1, 2, 3, 4]
#guard Iterator.toList (APPairIter.make (APPair.mk (-1) 5) 10) == [(10:Int), 9, 8, 7, 6]
#guard Iterator.toList (APPairIter.make (APPair.mk (-2) 5) 3) == [(3:Int), 1, -1, -3, -5]

end APPairIter

def APPairs := List APPair

namespace APPairs

abbrev Iter := Iterator (LEList APPairIter) (List Int)

def inst : Iter := inferInstance

private def lelist (pairs : APPairs) (start : Nat) : LEList APPairIter :=
  LEList.make $ pairs.map fun p => APPairIter.make p start

#guard Iterator.toList (lelist [APPair.mk 1 1] 0)  == [[(0:Int)]]
#guard Iterator.toList (lelist [APPair.mk 1 2] 0)  == [[(0:Int)], [1]]
#guard Iterator.toList (lelist [APPair.mk 1 3] 0)  == [[(0:Int)], [1], [2]]
#guard Iterator.toList (lelist [APPair.mk 1 3] 10)  == [[(10:Int)], [11], [12]]

#guard Iterator.toList (lelist [APPair.mk 1 2, APPair.mk 1 3] 0)
  == [[(0:Int), 0], [1, 0], [0, 1], [1, 1], [0, 2], [1, 2]]

#guard (Iterator.toList (lelist [APPair.mk 1 1, APPair.mk 1 2, APPair.mk 1 2] 0) : List (List Int))
  == [[(0:Int), 0, 0], [0, 1, 0], [0, 0, 1], [0, 1, 1]]

end APPairs

def AccessPattern.lelist (p : AccessPattern) : Err (LEList APPairIter) := do
  let parOff <- p.partitionRowOffset
  let freeOff <- p.freeElementOffset
  let parDimIter := APPairIter.make (APPair.mk 1 p.parNum) parOff
  -- Only the first free dimension gets an offset
  let freeIters := match p.freePattern with
  | [] => []
  | p :: ps => APPairIter.make p freeOff :: ps.map fun p => APPairIter.make p 0
  return LEList.make $ parDimIter :: freeIters

private def evalIndex (index : Core.Index) : Err TensorLib.Index.NumpyItem := match index with
| .coord n => .ok $ TensorLib.Index.NumpyItem.int n
| .slice s => do
  let s <- TensorLib.Slice.make (some s.l) (some s.u) (some s.step)
  .ok $ TensorLib.Index.NumpyItem.slice s

-- Lol to the name...
def evalValue (v : Core.Value) : WithEnv EValue := match v with
| .var x => do
  match (<- lookup x) with
  | none => throw s!"No variable {x} in the environment"
  | some t => return t
| .bool b => return .EBool b
| .int n => return .EInt n
| .float n => return .EFloat n
| .access a => return .EAccess a

def read (access : Core.Access) : WithEnv Tensor := match access with
| .simple tname => lookupTensor tname.name
| .basic access => do
  let tname := access.tensor
  let t <- lookupTensor tname.name
  let () <- checkIOTensor tname t
  let numpyBasic <- lift (access.indexes.mapM evalIndex)
  let t' <- TensorLib.Index.apply numpyBasic t
  return t'
| .pattern pattern => do
  let tname := pattern.tensor
  let t <- lookupTensor tname.name
  let () <- checkIOTensor tname t
  let shape := evalShape pattern.shape
  let mut res := TensorLib.Tensor.zeros t.dtype shape
  let mut apIter <- AccessPattern.lelist pattern
  let shapeIter := TensorLib.Shape.belist shape
  if Iterator.size (List Int) apIter != Iterator.size (List Nat) shapeIter then throw "invariant violation: iterator size mismatch" else
  for resIndex in shapeIter do
    let index : List Int := Iterator.peek apIter
    let apIter' <- match Iterator.next (List Int) apIter with
    | none => throw "iterator failed"
    | some iter =>
    apIter := iter
    let index <- index.mapM fun i => if i < 0 then throw "negative index" else return i.toNat
    let v <- t.getDimIndex index
    res <- res.setDimIndex resIndex v
  return res

def write (access : Core.Access) (v : Tensor) : WithEnv Unit := match access with
| .simple tname => insertTensor tname.name v
| .basic access => do
  let tname := access.tensor
  let t <- lookupTensor tname.name
  if t.shape != v.shape then throw "Shape mismatch" else
  let () <- checkIOTensor tname t
  let numpyBasic <- lift (access.indexes.mapM evalIndex)
  let t' <- TensorLib.Index.assign t numpyBasic v
  insertTensor tname.name t'
| .pattern pattern => do
  let tname := pattern.tensor
  let mut t <- lookupTensor tname.name
  let () <- checkIOTensor tname t
  let shape := evalShape pattern.shape
  if shape != v.shape then throw "Shape mismatch" else
  let mut apIter <- AccessPattern.lelist pattern
  let shapeIter := TensorLib.Shape.belist shape
  for vIndex in shapeIter do
    let index : List Int := Iterator.peek apIter
    let apIter' <- match Iterator.next (List Int) apIter with
    | none => throw "iterator failed"
    | some iter =>
    apIter := iter
    let tIndex <- index.mapM fun i => if i < 0 then throw "negative index" else return i.toNat
    let v <- t.getDimIndex tIndex
    let t' <- t.setDimIndex vIndex v
    t := t'
  insertTensor tname.name t

def evalExpr : Core.Expr -> WithEnv EValue
| .value v => evalValue v
| .call .. => throw "Unimplemented: call"

def evalStmt (stmt : Core.Stmt) : WithEnv Unit := match stmt with
| .ret v => do
  -- NB: This is weird. To evaluate a return, we shove a value with the special string "result" into the environment.
  let res <- evalValue v
  modify fun env => env.insert "result" res
| .assign x e => do
  let v <- evalExpr e
  modify fun env => env.insert x v
| .store dst (Operator.tensorScalar (TensorScalar.mk AluOp.add n false AluOp.bypass _ _)) [.access v] => do
  let dtype <- evalDtype v.tensor.dtype
  let v <- read v
  let n <- TensorLib.Tensor.arrayScalar dtype n.toLEByteArray
  let v <- TensorLib.Tensor.Ufunc.add v n
  write dst v
| .store _ (Operator.tensorScalar _) _
| .store _ (Operator.named _) _ => throw "Unimplemented: store"

/-
Returns a map where each key is the name of a tensor in kernel.outputs with the
corresponding computed value.
-/
def eval (kernel : Core.Kernel) (inputs : List Tensor) : WithEnv (List (String × Tensor)) := do
  checkInputTensors kernel inputs
  kernel.body.forM evalStmt
  checkOutputTensors kernel
  kernel.outputs.mapM fun tname => do
    let t <- lookupTensor tname.name
    return (tname.name, t)

end Eval
end KLR
