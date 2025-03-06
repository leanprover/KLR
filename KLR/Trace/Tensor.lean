/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.FromNKI

/-
# Tracing for Tensor related operations

TODO: These are just place holders...
-/
namespace KLR.Trace
open KLR.Core
open KLR.Trace.Builtin

namespace Tensor

-- This only handles the simple cases
-- Note: Maybe only simple cases are possible at this point ??
-- TODO: move to Access.shape
def inferShape : Access -> Err Shape
  | .basic t l =>
    match l with
    | [] => return t.shape
    | ix => do
        let base := t.shape.toList
        if base.length != ix.length then
          throw "unsupported index."
        let dims <- ix.mapM fun i =>
          match i with
          | .coord _ => return 0
          | .slice (some s) (some e) (some n) => do
              if s < 0 then throw "invalid start"
              if e <= s then throw "invalid end"
              if n <= 0 then throw "invalid step size"
              return ((e-s)/n).toNat
          | _ => throw s!"unsupported index"
        let shape <- Shape.fromList (dims.filter (. != 0))
        return shape
  | a => return a.shape

/-
Declare a new tensor, unique to the current expression.

We have to calculate how much memory we are going to use. The most memory we
could need is one tensor for each expression in the source program (loops can
reuse the same memory in each iteration). This code gives the name of the
tensor associated with an expression. Right now I am using the source location,
but we could also use a hash of expression, or something else. Note, this
expression may be evaluated many times, and we want this function to always
return the same result.

In the end we walk over the KLR kernel and collect all the TensorNames, and
these represent the memory we need to allocate in the dram, sbuf, etc.
-/
def declare (tag : String)
            (dtype : Dtype) (shape : Shape) (memory : Memory)
            : Trace TensorName := do
  let pos := (<- get).pos
  let tname := s!"{tag}.{pos.lineno}.{pos.col_offset}"
  return {
    name := tname
    dtype := dtype
    shape := shape
    address := {
        memory := memory
        size   := Address.defaultSize shape dtype
    }
  }

-- APIs

-- conversion to NKI

private def some_none : Option Term :=
  some .none

private def some_bool (b : Bool) : Option Term :=
  some (.expr (.value (.bool b)) .bool)

private def some_int (i : Int) : Option Term :=
  some (.expr (.value (.int i)) .int)

private def some_string (s : String) : Option Term :=
  some (.string s)

/-
TODO: These definitions are very verbose, but this pattern could be made more
convenient with a command macro, maybe something like:

#nki ndarray(shape:Shape, dtype:Dtype, memory:Memory = .sbuf) := do
  let t <- declare "t" dtype shape memory
  ...
-/
def ndarray : BuiltinFn :=
  withArgs [("shape", none),
            ("dtype", none),
            ("buffer", some_string "nki.language.sbuf")]
  fun
  | [shape, dtype, buf] => do
      let shape <- fromNKI? shape
      let dtype <- fromNKI? dtype
      let memory <- fromNKI? buf
      let t <- declare "ndarray" dtype shape memory
      let e := Expr.value (.access (.simple t))
      return .expr e (.tensor dtype shape)
  | _ => throw "invalid arguments"

def load : BuiltinFn :=
  withArgs [("src", none),
            ("mask", some_none),
            ("dtype", some_string "float32")]
  fun
  | [t, _, dtype] => do
      let acc <- fromNKI? t
      let shape <- inferShape acc
      let dtype <- fromNKI? dtype
      let dst <- declare "load" dtype shape .sbuf
      return .store (.simple dst) (.named "Load") [.access acc]
  | _ => throw "invalid arguments"

def store : BuiltinFn :=
  withArgs [("dst", none),("value", none)]
  fun
  | [dst, src] => do
      let a₁ <- fromNKI? dst
      let a₂ <- fromNKI? src
      let s₁ <- inferShape a₁
      let s₂ <- inferShape a₂
      if s₁ != s₂ then
        throw s!"incompatible shapes {s₁} {s₂}"
      return Term.store a₁ (.named "Store") [.access a₂]
  | _ => throw "invalid arguments"

def tensor_scalar : BuiltinFn :=
  withArgs [("data", none),
            ("op0", none),
            ("operand0",none),
            ("reverse0", some_bool false),
            ("op1", some_none),
            ("operand1", some_none),
            ("reverse1", some_bool false),
            ("dtype", some_none)]
  fun
  | [data, op0, operand0, reverse0, op1, operand1, reverse1, dtype] => do
      let acc <- fromNKI? data
      let shape <- inferShape acc
      let dtype := fromNKI Dtype.float32 dtype
      let op : TensorScalar := {
           op0 := <- fromNKI? op0
           const0 := <- fromNKI? operand0
           reverse0 := fromNKI false reverse0
           op1 := fromNKI .bypass op1
           const1 := fromNKI 0.0 operand1
           reverse1 := fromNKI false reverse1
           }
      let op := Operator.tensorScalar op
      --let ty := TermType.tensor dtype shape
      let dst <- declare "tsc" dtype shape .sbuf
      return .store (.simple dst) op [.access acc]
  | _ => throw "invalid arguments"

end Tensor

--------
-- TODO: These are just placeholdrs for the python operators

-- Unary operations on tensors

set_option linter.unusedVariables false
def tensor_op (op : UnaryOp) (t : Access) : Trace Term :=
  throw "unimp"

-- Binary operations on tensors / scalars

def tensor_tensor (op : BinOp) (l r : Access) : Trace Term :=
  throw "unimp"

def tensor_scalar (op : BinOp) (t : Access) (v : Value) : Trace Term :=
  throw "unimp"

def scalar_tensor (op : BinOp) (v : Value) (t : Access) : Trace Term :=
  throw "unimp"
