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

import KLR.Core

namespace KLR.Core

-- Compute Engines
inductive Engine where
  | unassigned
  | act | dma | dve | pe | pool | sp
  deriving BEq, Repr

-- Memory types
inductive Memory where
  | hbm | sbuf | pmem | reg
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
    @[computed_field]
    isInt : Dtype -> Bool
    | .int8 | .int16 | .int64 | .int32
    | .uint8 | .uint16 | .uint32 | .uint64 => true
    | _ => false

  deriving Repr, BEq

/-
ALU operations supported by the HW
Only used by: TensorScalar, TensorScalarPtr, TensorReduce, TensorTensor
-/

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

namespace AluOp

def isBitwise : AluOp -> Bool
  | arith_shift_left
  | arith_shift_right
  | bitwise_not
  | bitwise_and
  | bitwise_or
  | bitwise_xor
  | logical_shift_left
  | logical_shift_right
  | bypass => true
  | _ => false

def isArith : AluOp -> Bool
  | .bypass => true
  | op => not op.isBitwise

instance : ToString AluOp where
  toString op := reprStr op

end AluOp

-- TODO: should these be Int32 and Float32?
-- At the python level: no, after tracing: yes.
-- Perhaps FromNKI can check for overflow and raise an error?
inductive Const where
  | int (i : Int)
  | float (f : Float)
  deriving BEq, Repr

namespace Const

def isInt : Const -> Bool
  | .int _ => true | _ => false

def isFloat : Const -> Bool
  | .float _ => true | _ => false

instance : ToString Const where
  toString
  | .int i => toString i
  | .float f => toString f

end Const

-- Tensor-Scalar operator
-- Note: this is not supported in NKI, but it useful for testing.
structure TensorScalar where
  op0 : AluOp
  const0 : Float32
  reverse0 : Bool
  op1 : AluOp
  const1 : Float32
  reverse1 : Bool
  deriving Repr, BEq

-- Tensor-Scalar where the scalars are loaded from memory
structure TensorScalarAddr where
  op0 : AluOp
  reverse0 : Bool
  op1 : AluOp
  reverse1 : Bool
  deriving Repr, BEq

abbrev Opcode := UInt16

structure OutputTensor3d where -- TODO
  freePattern: List APPair
  offset : Nat := 0
  dtype : Dtype

structure InputTensor3d extends PseudoTensor3d where  -- TOOD
  parNum : Nat

inductive Immediate where
| register -- : TODO
| pointer -- : TODO
| int (i : Int32)
| float (f : Float32)
deriving BEq, Repr

inductive ActivationImm where
| register -- : TODO
| pointer -- : TODO
| float (f : Float32)
deriving BEq, Repr

inductive DropoutThresholdType
| DropRate
| KeepRate

structure Dropout where
    src_mem_pattern:       InputTensor3d
    dst_mem_pattern:       OutputTensor3d
    threshold_type:        DropoutThresholdType
    threshold:             Immediate

inductive AccumCmd where
| Idle
| Zero
| Accumulate
| ZeroAccumulate
| LoadAccumulate

structure Activate where
    accumulator_cmd:       AccumCmd
    src_mem_pattern:       InputTensor3d
    in_bias_dtype:         (Dtype × Dtype)
    activation_func:       u8
    scale_value:           Immediate
    bias:                  Immediate
    imm:                   Immediate
    dst_mem_pattern:       OutputTensor3d
}

structure Reciprocal where
-- pub struct s4d4_tr_struct {
--     pub header:                Header,          // 4    ( 0 -  3)
--     pub events:                Events,          // 8    ( 4 - 11)
--     pub src_mem_pattern:       MemPattern4d,    // 20   (12 - 31)
--     pub in_dtype:              Dtype,           // 1    (32     )
--     pub out_dtype:             Dtype,           // 1    (33     )
--     pub num_active_channels:   u8,              // 1    (34     )
--     pub negated:               u8,              // 1    (35     )
--     pub op:                    AluOp,           // 1    (36     )
--     pub op_dim:                TensorSubdim,    // 1    (37     )
--     pub mask_enable:           u8,              // 1    (38     )
--     pub reserved1:             [u8;5],          // 5    (39 - 43)
--     pub dst_mem_pattern:       MemPattern4d,    // 20   (44 - 63)
-- }

structure Copy where
-- pub struct s4d4_tr_struct {
--     pub header:                Header,          // 4    ( 0 -  3)
--     pub events:                Events,          // 8    ( 4 - 11)
--     pub src_mem_pattern:       MemPattern4d,    // 20   (12 - 31)
--     pub in_dtype:              Dtype,           // 1    (32     )
--     pub out_dtype:             Dtype,           // 1    (33     )
--     pub num_active_channels:   u8,              // 1    (34     )
--     pub negated:               u8,              // 1    (35     )
--     pub op:                    AluOp,           // 1    (36     )
--     pub op_dim:                TensorSubdim,    // 1    (37     )
--     pub mask_enable:           u8,              // 1    (38     )
--     pub reserved1:             [u8;5],          // 5    (39 - 43)
--     pub dst_mem_pattern:       MemPattern4d,    // 20   (44 - 63)
-- }


-- All of the operators
inductive Operator where
  | load : Operator
  | save : Operator
  | memset : Nat -> Operator /- the Nat operand is uint32_t -/
  | tensorScalar : TensorScalar -> Operator
  | tensorScalarAddr : TensorScalarAddr -> Operator
  deriving Repr, BEq
