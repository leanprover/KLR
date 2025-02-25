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

-- List of builtin function implementations
def NKIBuiltins : List (Name × BuiltinFn) :=
  [ (nl "load", Tensor.load)
  , (nl "store", Tensor.store)
  , (nl "ndarray", Tensor.ndarray)
  , (nisa "tensor_scalar", Tensor.tensor_scalar)
  ]

-- NKI environment, including constants and the names of builtin functions
def NKIEnv : List (Name × Term) :=
  [ module nki
  , module nki_isa
  , module nki_lang
  , const_int (.str (nl "tile_size") "pmax") 128
  ]
  ++ NKIBuiltins.map fun (x,_) => (x, .builtin x (.obj x))
