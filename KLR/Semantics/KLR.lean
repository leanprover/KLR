/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.NML
import KLR.Semantics.Memory
/-
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
  -- NB. This model ignores the `count` field and sets the entire tensor to imm.
  let imm := @op.value.semantics DataT float_interp
  match op.dst with
  | .sbuf _     => .error "Semantics not defined"
  | .hbm v      =>
      -- By virtue of using an Operand,
      -- a programmer has given a specific index into the HBM to set the memory of.
      match v.dims with
      -- For right now, only model contiguous memsets
      -- | [⟨1, n⟩] => imm |>.bind (fun x => .ok <| .set_phys_hbm_area v.address n x)
      | _ => .error "Semantics not defined"
  | .psum _     => .error "Semantics not defined"
  | .register _ => .error "Semantics not defined"
  | .abstract _ => .error "Semantics not defined"
| rangeSelect        _ => .error "Semantics not defined"
| reciprocal         _ => .error "Semantics not defined"
| scalarTensorTensor _ => .error "Semantics not defined"
| shuffle            _ => .error "Semantics not defined"
| tensorReduce       _ => .error "Semantics not defined"
| tensorScalar       _ => .error "Semantics not defined"
| tensorTensor       _ => .error "Semantics not defined"
| tensorTensorScan   _ => .error "Semantics not defined"
| transpose          _ => .error "Semantics not defined"
|                    _ => .error "Semantics not defined"

def KLR.Core.Stmt.semantics : KLR.Core.Stmt → Err (@NML.Stmt DataT)
| .ret v => @v.semantics DataT float_interp |>.bind (.ok <| .ret <| .val ·)
| .assign x e => @e.semantics DataT float_interp |>.bind (.ok <| .assign (some x) ·)
-- | .oper op => @KLR.Core.Operator.semantics DataT float_interp op
| _ => .error "Semantics not defined"

-- Default AffineMap (row major form)
def AffineMap.ofShape (s : KLR.Core.Shape) : AffineMap where
  free_offset  := 0
  free_strides := s.freeDims.map (fun _ => 1)
  par_offset   := 0
  par_stride   := 1

theorem AffineMap.ofShape_wf : (AffineMap.ofShape s).free_strides.length = s.freeDims.length := by
  simp [AffineMap.ofShape]

/-- Return fresh HBM pointers for input and output tensors.
NB. The variable names given to each tensor pointer are derived from the tensor name itself,
so tensors with the same name will shadow each other. -/
def KLR.Core.Address.toInputOutputPointer (i : Nat) (n : KLR.Core.TensorName) : Err (String × @NML.Value DataT) :=
  match n.address.parOffset, n.address.freeOffset with
  | .none, .none =>
      let h : NML.TensorHandle := {
        index := .hbmIndex i
        layout := AffineMap.ofShape n.shape
        shape := n.shape
        layout_wf := AffineMap.ofShape_wf
        dtype := n.dtype
        name := .some n.name
      }
      .ok (n.name, NML.Value.ptr h)
  | _, _ => .error "Input tensors must not have memory location specified"


def BindingsToLocals : List (String × @NML.Value DataT) → @NML.LocalContext DataT :=
  List.foldl (fun ℓ ⟨s, v⟩ => ℓ.bindv s v) .emp

/-- Transform a KLR kernel into its NML program interpretation.
To perform this transformation, you must provide a datatype to interpret floats into,
as well as a partial function for interpreting floats into that type. -/
def KLR.Core.Kernel.semantics (k : KLR.Core.Kernel) : Err (@NML.ExecState DataT) :=
  List.mapM (KLR.Core.Stmt.semantics (DataT := DataT) (float_interp := float_interp)) k.body |>.bind fun p =>
  -- Set up pointers to HBM for each of the input tensors
  List.mapIdxM (@KLR.Core.Address.toInputOutputPointer DataT) (k.inputs ++ k.outputs) |>.bind fun L =>
  .ok <| .run p (BindingsToLocals L)
-/
