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

-- decompose a tensor expresssion
def Expr.inferTensor : Expr -> Err (TensorName × List Index)
  | .tensor t => return (t, [.ellipsis])
  | .access t ix => do
      match <- inferTensor t with
      | (t, [.ellipsis]) => return (t, ix)
      | _ => throw "unsupported tensor expression"
  | _ => throw "expecting tensor expression"

def Term.inferTensor : Term -> Err (TensorName × List Index)
  | .expr e _ => Expr.inferTensor e
  | _ => throw "expecting tensor"

-- This only handles the simple cases
-- Note: Maybe only simple cases are possible at this point ??
def inferShape (t : TensorName) : List Index -> Err Shape
  | [] | [.ellipsis] => return t.shape
  | ix => do
      let base := t.shape
      if base.length != ix.length then
        throw "unsupported index"
      let dims <- (base.zip ix).mapM fun (x, i) =>
        match i with
        | .coord _ => return 0
        | .slice none none none
        | .slice (some (.int 0)) none none => return x
        | .slice none (some (.int i)) none
        | .slice (some (.int 0)) (some (.int i)) none => return i.toNat
        | _ => throw "unsupported index"
      return dims.filter (. != 0)

def Expr.inferShape (e : Expr) : Err Shape := do
  let (t, ix) <- inferTensor e
  Tensor.inferShape t ix

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
            : TraceM TensorName := do
  let pos := (<- get).pos
  let tname := s!"{tag}.{pos.lineno}.{pos.col_offset}"
  return {
    name := tname
    dtype := dtype
    shape := shape
    memory := memory
    }

-- generate a store expression based on the src shape
def store_expr (tag : String)
               (dtype : Dtype) (memory : Memory) (src : Term)
               : TraceM Term := do
  match src with
  | .expr e (.tensor _ shape) => do
      let dst <- declare tag dtype shape memory
      return .store dst [.ellipsis] e
  | .expr e _ => do
      let shape <- Expr.inferShape e
      let dst <- declare tag dtype shape memory
      return .store dst [.ellipsis] e
  | _ => throw "expecting tensor in store"

-- APIs

-- conversion to NKI

private def some_none : Option Term :=
  some (.expr (.const .none) .none)

private def some_bool (b : Bool) : Option Term :=
  some (.expr (.const (.bool b)) .bool)

private def some_int (i : Int) : Option Term :=
  some (.expr (.const (.int i)) .int)

private def some_string (s : String) : Option Term :=
  some (.expr (.const (.string s)) .string)

/-
TODO: These definitions are very verbose, but this pattern could be made more
convenient with a command macro, maybe something like:

#nki ndarray(shape:Shape, dtype:Dtype, memory:Memory = .sbuf) := do
  let t <- declare "t" dtype shape memory
  ...
-/
def ndarray : GlobalFn :=
  withArgs [("shape", none),
            ("dtype", none),
            ("buffer", some_string "nki.language.sbuf")]
  fun
  | [shape, dtype, buf] => do
      let shape <- fromNKI? shape
      let dtype <- fromNKI? dtype
      let memory <- fromNKI? buf
      let t <- declare "ndarray" dtype shape memory
      return .expr (.tensor t) (.tensor dtype shape)
  | _ => throw "invalid arguments"

def load : GlobalFn :=
  withArgs [("src", none),
            ("mask", some_none),
            ("dtype", some_string "float32")]
  fun
  | [t, _, dtype] => do
      let dtype <- fromNKI? dtype
      store_expr "load" dtype .sbuf t
  | _ => throw "invalid arguments"

def store : GlobalFn :=
  withArgs [("dst", none),("value", none)]
  fun
  | [.expr dst _, .expr src _] => do
      let (t₁, i₁) <- Expr.inferTensor dst
      let (t₂, i₂) <- Expr.inferTensor src
      let s₁ <- inferShape t₁ i₁
      let s₂ <- inferShape t₂ i₂
      if s₁ != s₂ then
        throw s!"incompatible shapes {s₁} {s₂}"

      let src := Expr.access (.tensor t₂) i₂
      return Term.store t₁ i₁ src
  | _ => throw "invalid arguments"

def tensor_scalar : GlobalFn :=
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
      let (t, ix) <- Term.inferTensor data
      let shape <- inferShape t ix
      let dtype := fromNKI Dtype.float32 dtype
      let op : TensorScalar := {
           op0 := <- fromNKI? op0
           const0 := <- fromNKI? operand0
           reverse0 := fromNKI false reverse0
           op1 := fromNKI .bypass op1
           const1 := fromNKI 0.0 operand1
           reverse1 := fromNKI false reverse1
           }
      let e := Expr.operator (.tensorScalar op)
      let ty := TermType.tensor dtype shape
      let e := Expr.call e [.access (.tensor t) ix] []
      store_expr "tsc" dtype .sbuf (.expr e ty)
  | _ => throw "invalid arguments"

end Tensor

--------
-- TODO: These are just placeholdrs for the python operators

private def tensor_call (op : String) (args : List Expr) : Term :=
  let type := if let .tensor t :: _ := args
              then TermType.tensor t.dtype t.shape
              else TermType.obj "object".toName
  let name := Expr.var ("tensor_".append op)
  .expr (.call name args []) type

-- Unary operations on tensors

def tensor_op (op : UnaryOp) (t : TensorName) : TraceM Term :=
  let op := toString (repr op)
  return tensor_call op [.tensor t]

-- Binary operations on tensors / scalars

def tensor_tensor (op : BinOp) (l r : TensorName) : TraceM Term :=
  let op := toString (repr op)
  return tensor_call op [.tensor l, .tensor r]

private def broadcast (t : TensorName) (c : Const) : Expr :=
  let args := t.shape.map fun i => Expr.const (.int $ .ofNat i)
  let args := .const c :: args
  .call (.var "broadcast") args []

def tensor_scalar (op : BinOp) (t : TensorName) (c : Const) : TraceM Term :=
  let op := toString (repr op)
  return tensor_call op [ .tensor t, broadcast t c]

def scalar_tensor (op : BinOp) (c : Const) (t : TensorName) : TraceM Term :=
  let op := toString (repr op)
  return tensor_call op [ .tensor t, broadcast t c]
