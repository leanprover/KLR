/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Tensor

/-
# NKI built-ins

This module defines the builtin constants used by tracing for NKI kernels.
-/
namespace KLR.Trace
open KLR.Core
open KLR.Trace.Builtin

private def nki : Name := .str .anonymous "nki"
private def nki_isa : Name := .str nki "isa"
private def nki_lang : Name := .str nki "language"

private def nl : String -> Name := .str nki_lang
private def nisa : String -> Name := .str nki_isa

/-
Note: this object contains a bunch of architecture parameters that
need to be set according to which HW we are compiling for.
TODO: figure out the mechanism for this.
-/
def tile_size : Global :=
  let name := nl "tile_size"
  { name := name
  , attr := attrs
  , call := uncallable name
  }
where
  attrs : GlobalAttr
  | "pmax" => return .expr (.const $ .int 128) .int
  | a => throw s!"unsupported attribute {a}"

/-
This is a place-holder for arange.
Note: arange is a bit inconsistent, and perhaps we should just use numpy.arange
and later convert advanced indexing to basic indexing (when possible)
-/
structure ARange where
  arg : Int  -- argument to arange
  ndx : Nat  -- location of slice index

instance : Obj ARange where
  name := "arange".toName
  index := fun _ _ _ => .ok (.coord $ some $ .int 0)

def arange : Global :=
  { name := name
  , attr := noAttr name
  , call := noKWArgs range
  }
where
  name := nl "arange"
  range : List Term -> TraceM Term
  | [ .expr (.const (.int i)) _ ] => do
      return .object {
        name := name
        attr := noAttr name
        access := arange_access i
        index := noIndex name
        binop := noBinop name
        call := uncallable name
      }
  | _ => throw "invalid arguments"
  arange_access (i : Int) (l : List Index) : Err Term := do
    let (l₁, l₂) := l.enum.partition fun x => x.snd == .slice none none none
    let all_none := l₂.all fun x => x.snd == .coord none
    if not all_none then
      throw "arange only supports None and slice indexes"
    if h:l₁.length = 1 then
      let (n,_) := l₁[0]
      return .object (toObject (ARange.mk i n))
    else
      throw "arange subscript must have exactly one slice"

def NKIEnv : List (Name × Item) :=
  [ module nki
  , module nki_isa
  , module nki_lang
  , global tile_size
  , global arange
  , globalFn (nl "ndarray") Tensor.ndarray
  , globalFn (nl "load") Tensor.load
  , globalFn (nl "store") Tensor.store
  , globalFn (nisa "tensor_scalar") Tensor.tensor_scalar
  ]
