/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

/-
# Definition of operators

Operators can appear in a call node, and can be thought of as functions that
take arguments and return results. However, an operator may have several
variations, and these variations show up as parameters within the operator and
not as arguments of the call node. A typical example is:

  .store t [] (.call (.operator (.tensorScalar ts)) [a,b] [])

where `ts` contains the tensor scalar parameters:

  let ts := TensorScalar { op0 := .add, ..}
  let ts := TensorScalar { op0 := .multiply, op1 := add, ..}

The choice of argument or parameter may seem arbitrary; these definitions
follow the hardware ISA as close as possible.
-/
namespace KLR.Core

-- Compute Engines
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, Repr

-- Memory types
inductive Memory where
  | dram | sbuf | pmem | reg
  deriving Repr, BEq

/-
Tensor element types supported by HW and available from NKI.

The HW always performs operations on 32-bit types. However, when reading from
or writing to memory, automatic conversion to and from the following types is
supported.
-/
inductive Dtype where
  | bfloat16
  | float8e3 | float8e4 | float8e5
  | float16 | float32 | float32r
  | int8 | int16 | int64 | int32
  | uint8 | uint16 | uint32 | uint64
  with
    @[computed_field]
    size : Dtype -> Nat
    | .uint8 | .int8 | .float8e3 | .float8e4 | .float8e5 => 1
    | .uint16 | .int16 | .bfloat16 | .float16 => 2
    | .uint32 | .int32 | .float32 | .float32r => 4
    | .uint64 | .int64 => 8
  deriving Repr, BEq

-- ALU operations supported by the HW
-- TODO organize these into groups to make seantic checking easier
inductive AluOp where
  | abs
  | add
  | arith_shift_left
  | arith_shift_right
  | average
  | bitwise_and
  | bitwise_not
  | bitwise_or
  | bitwise_xor
  | bypass
  | divide
  | elemwise_mul
  | is_equal
  | is_ge
  | is_gt
  | is_le
  | is_lt
  | logical_and
  | logical_or
  | logical_shift_left
  | logical_shift_right
  | logical_xor
  | max
  | min
  | mod
  | mult
  | not_equal
  | pow
  | rsqrt
  | subtract
  deriving BEq, Repr

-- Tensor-Scalar operator
-- TODO: this is gen1 only, add gen2
structure TensorScalar where
  op0 : AluOp
  const0 : Float
  reverse0 : Bool
  op1 : AluOp
  const1 : Float
  reverse1 : Bool
  deriving Repr, BEq

-- All of the operators
inductive Operator where
  | tensorScalar : TensorScalar -> Operator
  deriving Repr, BEq
