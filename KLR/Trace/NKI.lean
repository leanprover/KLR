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

private def nki_ : Name := .str .anonymous "nki"
private def nki_isa : Name := .str nki_ "isa"
private def nki_lang : Name := .str nki_ "language"

private def nl : String -> Name := .str nki_lang
private def nisa : String -> Name := .str nki_isa

-- List of builtin function implementations
def NKIBuiltins : List (Name × BuiltinFn) :=
  [ (nl "load", Tensor.load)
  , (nl "store", Tensor.store)
  , (nl "zeros", Tensor.zeros)
  --, (nl "ndarray", Tensor.ndarray) see comment in Tensor.lean
  , (nisa "tensor_scalar", Tensor.tensor_scalar)
  ]

-- NKI environment, including constants and the names of builtin functions
def NKIEnv : List (Name × Term) :=
  [ module nki_
  , module nki_isa
  , module nki_lang
  , const_int (.str (nl "tile_size") "pmax") 128
  , const_int (.str (nl "tile_size") "gemm_stationary_fmax") 128
  , const_int (.str (nl "tile_size") "gemm_moving_fmax") 512
  , const_var (nl "shared_hbm")
  , const_var (nl "private_hbm")
  , const_var (nl "hbm")
  , const_var (nl "sbuf")
  , const_var (nl "psum")
  , (nl "mgrid", .mgrid)
  ]
  ++ NKIBuiltins.map fun (x,_) => (x, .builtin x (.obj x) none)
