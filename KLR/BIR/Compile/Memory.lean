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

Create Allocations for each named tensor. The access pattern compiler (below)
needs to know how the physical memory is defined for each tensor. For now, all
tensors have the same basic layout.
-/

-- TODO: just a for instance...
def physicalShape (t : TensorName) : List Nat :=
  match t.dtype, t.shape.toList with
  | .float16, [x, y] => [x, y * 2]
  | .float32, [x, y] => [x, y * 4]
  | _, _ => t.shape.toList -- TODO incorrect

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
    ap := [ [ d2, d1 ], [ 1, d2 ] ]
    dtype := "" -- filled in below
    offset := 0
    memsetref := "" -- filled in below
    memref := "" -- filled in below
  }

def slicesToAP (d1 d2 : Nat) : List Index -> Compile PhysicalAccessPattern
  | [ .slice none none none, .slice none none none ] => dimToAP d1 d2
  | [ .slice none (some a) none,
      .slice none (some b) none ] => do
        if a < 0 || b < 0 then
          throw "negative slice patterns not supported"
        let a := a.toNat
        let b := b.toNat
        if a < d1 || b < d2 then
          throw "partial slice patterns not supported"
        dimToAP a b
  | _ => throw "unimplemented access pattern"

def pairsToAP (offset : Nat) (aps : List APPair) : PhysicalAccessPattern :=
  {
    ap := aps.map fun ap => [ap.step, ap.num]
    dtype := "" -- filled in below
    offset := offset
    memsetref := "" -- filled in below
    memref := "" -- filled in below
  }

private def setMemRef (t : TensorName) (ap : PhysicalAccessPattern) : PhysicalAccessPattern :=
  { ap with
    dtype := toString (Std.format t.dtype)
    memsetref := t.name ++ "_set"
    memref := t.name
  }

def accessToAP : Access -> Compile PhysicalAccessPattern
  | .simple t@{ shape := ⟨ a, [b] ⟩, .. } => do
      let ap <- dimToAP a b
      return (setMemRef t ap)
  | .basic t@{ shape := ⟨ a, [b] ⟩, ..} ix => do
      let ap <- slicesToAP a b ix
      return (setMemRef t ap)
  | .pattern t ap => do
      let ap := pairsToAP ap.offset (⟨1, ap.parNum⟩ :: ap.freePattern )
      return (setMemRef t ap)
  | _ => throw "unsupported access"
