/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import KLR.Core
import KLR.Trace.Types
import KLR.Trace.Builtin
import KLR.Trace.Tensor
import KLR.Trace.ISA

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
  --, (nisa "tensor_scalar", Tensor.tensor_scalar)
  , (nisa "dma_copy", Isa.dma_copy)
  , (nisa "activation", Isa.activation)
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
  , const_var (nl "exp")
  , (nl "mgrid", .mgrid)
  ]
  ++ NKIBuiltins.map fun (x,_) => (x, .builtin x (.obj x) none)
