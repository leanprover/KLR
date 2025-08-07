/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.NML
import KLR.Semantics.Memory

/- # Semantics for KLR by translation to NML -/

open KLR.Core

variable {DataT : Type}
variable {float_interp : Float → KLR.Err DataT}

def KLR.Core.Value.semantics : KLR.Core.Value → Err (@NML.Value DataT)
| bool b => .ok <| .bool b
| int i => .ok <| .int i
| float f => (float_interp f).map .data
| _ => .error "Semantics not defined"

def KLR.Core.Expr.semantics : KLR.Core.Expr → Err (@NML.Expr DataT)
| .value v => @v.semantics DataT float_interp |>.bind (.ok <| NML.Expr.val ·)
| _ => .error "Semantics not defined"

def KLR.Core.TensorRef.semantics : KLR.Core.TensorRef → Err Nat
-- | .sbuf _ => sorry
| _ => .error "Semantics not defined"

-- Since immediates can be registers, I'll give their semantics as an Expr.
def KLR.Core.Immediate.semantics : KLR.Core.Immediate → Err (@NML.Expr DataT)
| .int i   => .ok <| .val <| .int i.toInt
| .float f => (float_interp f.toFloat) |>.bind (.ok <| .val <| .data ·)
| _ => .error "Semantics not defined"

def KLR.Core.Operator.semantics : KLR.Core.Operator → Err (@NML.Stmt DataT)
| activate           _ => .error "Semantics not defined"
| affineSelect       _ => .error "Semantics not defined"
| batchNormAggregate _ => .error "Semantics not defined"
| batchNormStats     _ => .error "Semantics not defined"
| copy               _ => .error "Semantics not defined"
| copyPredicated     _ => .error "Semantics not defined"
| dmaCopy            _ => .error "Semantics not defined"
| dmaTranspose       _ => .error "Semantics not defined"
| dropout            _ => .error "Semantics not defined"
| findIndex8         _ => .error "Semantics not defined"
| iota               _ => .error "Semantics not defined"
| loadMaskRegister   _ => .error "Semantics not defined"
| loadStationary     _ => .error "Semantics not defined"
| localGather        _ => .error "Semantics not defined"
| matMul             _ => .error "Semantics not defined"
| matchReplace8      _ => .error "Semantics not defined"
| matchValueLoad     _ => .error "Semantics not defined"
| max8               _ => .error "Semantics not defined"
| memSet             op =>
  let dst := op.dst.semantics
  let imm := @op.value.semantics DataT
  match op.count with
  | 1 => sorry
  | _ => .error "Semantics not defined"
| rangeSelect        _ => .error "Semantics not defined"
| reciprocal         _ => .error "Semantics not defined"
| scalarTensorTensor _ => .error "Semantics not defined"
| shuffle            _ => .error "Semantics not defined"
| tensorReduce       _ => .error "Semantics not defined"
| tensorScalar       _ => .error "Semantics not defined"
| tensorTensor       _ => .error "Semantics not defined"
| tensorTensorScan   _ => .error "Semantics not defined"
| transpose          _ => .error "Semantics not defined"

def KLR.Core.Stmt.semantics : KLR.Core.Stmt → Err (@NML.Stmt DataT)
| .ret v => @v.semantics DataT float_interp |>.bind (.ok <| .ret <| .val ·)
| .assign x e => @e.semantics DataT float_interp |>.bind (.ok <| .assign (some x) ·)
| .oper op => KLR.Core.Operator.semantics op
| _ => .error "Semantics not defined"
