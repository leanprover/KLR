/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.BIR.Compile.Types

/-
Memory handling routines for the KLR to BIR compiler
-/

namespace KLR.BIR.Compile
open KLR.Core

/-
# Memory allocation

Create Allocations for each named tensor.
-/

def physicalShape (t : TensorName) : List Nat :=
  let sz := t.dtype.size
  t.shape.parDim :: t.shape.freeDims.map (. * sz)

-- Create memory region corresponding to a named tensor
def allocate (kind : TensorKind) (t : TensorName) : Compile Allocation := do
  let type : MemoryType :=
    match kind, t.address.memory with
    | .Input, _ => .Input
    | .Output, _ => .Output
    | _, .hbm => .DRAM
    | _, .sbuf => .SB
    | _, .pmem => .PSUM
    | _, .reg => .REG
  return {
    addr_space := some .Shared  -- LNC ?
    dtype := some t.dtype
    partition_dim := some 0
    tensor_shape := t.shape.toList
    name := t.name ++ "_set"
    kind := kind
    memorylocations := [{
        name := t.name
        type := type
        dims := physicalShape t
      }]
    }

/-
# Memory Access Patterns

Generate access patterns for tensor access expressions.
-/

-- Just to get things working, here are variations for full 2d tensors only
-- e.g. t[:,:] or t[...] or similar
def dimToAP (d1 d2 : Nat) : Compile PhysicalAccessPattern :=
  return {
    ap := [ { step := d2, num := d1 }, { step := 1, num := d2 } ]
    dtype := Dtype.uint8 -- filled in below
    offset := 0
    memsetref := "" -- filled in below
    memref := "" -- filled in below
  }

-- TODO: move to Core and make general
def slicesToAP (d1 d2 : Nat) : List Index -> Compile PhysicalAccessPattern
  | [ .slice (Slice.mk 0 b 1 _), .slice (Slice.mk 0 y 1 _)] => do
        if b != d1 || y != d2 then
          throw "partial slice patterns not supported"
        dimToAP d1 d2
  | _ => throw "unimplemented access pattern"

def pairsToAP (offset : Nat) (aps : List APPair) : PhysicalAccessPattern :=
  {
    ap := aps
    dtype := Dtype.uint8 -- filled in below
    offset := offset
    memsetref := "" -- filled in below
    memref := "" -- filled in below
  }

private def setMemRef (t : TensorName) (ap : PhysicalAccessPattern) : PhysicalAccessPattern :=
  { ap with
    dtype := t.dtype
    memsetref := t.name ++ "_set"
    memref := t.name
  }

def accessToAP : Access -> Compile PhysicalAccessPattern
  | .simple t@{ shape := ⟨ a, [b] ⟩, .. } => do
      let ap <- dimToAP a b
      return (setMemRef t ap)
  | .basic { tensor := t@{ shape := ⟨ a, [b] ⟩, ..} , indexes, .. } => do
      let ap <- slicesToAP a b indexes
      return (setMemRef t ap)
  | .pattern ap => do
      let ap' := pairsToAP ap.offset (⟨1, ap.parNum⟩ :: ap.freePattern )
      return (setMemRef ap.tensor ap')
  | _ => throw "unsupported access"
