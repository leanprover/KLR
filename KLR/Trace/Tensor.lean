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
def declare (name : String)
            (dtype : Dtype) (shape : Shape) (memory : Memory)
            : Trace TensorSram := do
  let pos := (<- get).pos
  let tname := s!"{name}.{pos.line}.{pos.column}"
  let size := Address.defaultSize shape dtype
  TensorSram.make tname dtype shape $ some {
    memory := memory
    parSize := size.1
    freeSize := size.2
  }

-- APIs
-- TODO  update once store is removed from KLR.Core

nki load (_src : Access) (_dtype : Dtype := .float32) := do
  --let shape <- src.shape
  --let dst <- declare "load" dtype shape .sbuf
  --return .store (.simple dst) .load [.access src]
  throw "unimp"

nki store (_dst : Access) (_value : Core.Value) := do
  --return Term.store dst .save [value]
  throw "unimp"

nki zeros (_shape : Shape) (_dtype : Dtype) (_buffer : Memory := .sbuf)
          (_name : String := "") := do
  --let dst <- declare ("zeros_" ++ name) dtype shape buffer
  --return .store (.simple dst) (.memset 0) []
  throw "unimp"

nki tensor_scalar (_data : Access)
                  (_op0 : AluOp)
                  (_operand0 : Float32)
                  (_reverse0 : Bool := False)
                  (_op1 : AluOp := .bypass)
                  (_operand1 : Float32 := 0.0)
                  (_reverse1 : Bool := false)
                  (_dtype : Dtype := .float32) := do
  --let shape <- data.shape
  --let op := Operator.tensorScalar {
  --  op0, const0 := operand0, reverse0,
  --  op1, const1 := operand1, reverse1,
  --}
  --let dst <- declare "tsc" dtype shape .sbuf
  --return .store (.simple dst) op [.access data]
  throw "unimp"

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
