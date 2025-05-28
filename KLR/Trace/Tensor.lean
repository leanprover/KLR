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

namespace Tensor

def inferShape : Access -> Err Shape := Access.shape

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
  TensorName.make tname dtype shape $ some {
    memory := memory
    size   := Address.defaultSize shape dtype
  }

-- APIs

nki load (src : Access) (dtype : Dtype := .float32) := do
  let shape <- src.shape
  let dst <- declare "load" dtype shape .sbuf
  return .store (.simple dst) .load [.access src]

nki store (dst : Access) (value : Core.Value) := do
  return Term.store dst .save [value]

nki zeros (shape : Shape) (dtype : Dtype) (buffer : Memory := .sbuf)
          (name : String := "") := do
  let dst <- declare ("zeros_" ++ name) dtype shape buffer
  return .store (.simple dst) .const [
      if dtype.isInt then .int 0 else .float 0.0]

nki tensor_scalar (data : Access)
                  (op0 : AluOp)
                  (operand0 : Float32)
                  (reverse0 : Bool := False)
                  (op1 : AluOp := .bypass)
                  (operand1 : Float32 := 0.0)
                  (reverse1 : Bool := false)
                  (dtype : Dtype := .float32) := do
  let shape <- data.shape
  let op := Operator.tensorScalar {
    op0, const0 := operand0, reverse0,
    op1, const1 := operand1, reverse1,
  }
  let dst <- declare "tsc" dtype shape .sbuf
  return .store (.simple dst) op [.access data]

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
