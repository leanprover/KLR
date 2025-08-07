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

private def neuronxcc : Name := .str .anonymous "neuronxcc"
private def nki_ : Name := .str neuronxcc "nki"
private def nki_isa : Name := .str nki_ "isa"
private def nki_lang : Name := .str nki_ "language"
private def nisa_cmd : Name := .str nki_isa "reduce_cmd"

private def nl : String -> Name := .str nki_lang
private def nisa : String -> Name := .str nki_isa

-- List of builtin function implementations
def NKIBuiltins : List (Name × BuiltinFn) :=
  [ (nl "load", Tensor.load)
  , (nl "store", Tensor.store)
  , (nl "zeros", Tensor.zeros)
  --, (nl "ndarray", Tensor.ndarray) see comment in Tensor.lean
  -- isa
  , (nisa "activation", Isa.activation)
  --, (nisa "affine_select", Isa.affine_select)
  , (nisa "bn_stats", Isa.bn_stats)
  , (nisa "bn_aggr", Isa.bn_aggr)
  , (nisa "tensor_copy", Isa.tensor_copy)
  , (nisa "tensor_copy_predicated", Isa.tensor_copy_predicated)
  , (nisa "dma_copy", Isa.dma_copy)
  , (nisa "dma_transpose", Isa.dma_transpose)
  , (nisa "dropout", Isa.dropout)
  , (nisa "nc_find_index8", Isa.nc_find_index8)
  , (nisa "iota", Isa.iota)
  -- TODO load mask register
  -- TODO load stationary
  -- TODO ISA Matmul
  , (nisa "nc_match_replace8", Isa.nc_match_replace8)
  -- TODO match value load
  , (nisa "max8", Isa.max8)
  , (nisa "memset", Isa.memset)
  , (nisa "range_select", Isa.range_select)
  , (nisa "select_reduce", Isa.select_reduce)
  , (nisa "sequence_bounds", Isa.sequence_bounds)
  , (nisa "local_gather", Isa.local_gather)
  , (nisa "reciprocal", Isa.reciprocal)
  , (nisa "nc_stream_shuffle", Isa.nc_stream_shuffle)
  , (nisa "tensor_reduce", Isa.tensor_reduce)
  , (nisa "tensor_tensor_scan", Isa.tensor_tensor_scan)
  , (nisa "nc_transpose", Isa.nc_transpose)
  , (nisa "nc_matmul", Isa.nc_matmul)
  , (nisa "activation_reduce", Isa.activation_reduce)
  , (nisa "tensor_partition_reduce", Isa.tensor_partition_reduce)
  , (nisa "tensor_scalar", Isa.tensor_scalar)
  , (nisa "scalar_tensor_tensor", Isa.scalar_tensor_tensor)
  , (nisa "tensor_tensor", Isa.tensor_tensor)
  , (nisa "tensor_scalar_reduce", Isa.tensor_scalar_reduce)
  , (nisa "tensor_copy_dynamic_src", Isa.tensor_copy_dynamic_src)
  , (nisa "tensor_copy_dynamic_dst", Isa.tensor_copy_dynamic_dst)
  ]

-- NKI environment, including constants and the names of builtin functions
def NKIEnv : List (Name × Term) :=
  [ module neuronxcc
  , module nki_
  , module nki_isa
  , module nki_lang
  , module nisa_cmd
  , const_int (.str (nl "tile_size") "pmax") 128
  , const_int (.str (nl "tile_size") "gemm_stationary_fmax") 128
  , const_int (.str (nl "tile_size") "gemm_moving_fmax") 512
  , const_var (nl "shared_hbm")
  , const_var (nl "private_hbm")
  , const_var (nl "hbm")
  , const_var (nl "sbuf")
  , const_var (nl "psum")
  , const_var (nl "exp")
  , const_var (nl "")
  , const_var (nl "add")
  , const_var (nl "subtract")
  , const_var (nl "multiply")
  , const_var (nl "maximum")
  , const_var (nl "minimum")
  , const_var (nl "equal")
  , const_var (nl "not_equal")
  , const_var (nl "greater_equal")
  , const_var (nl "greater")
  , const_var (nl "less_equal")
  , const_var (nl "less")
  , const_var (nl "logical_not")
  , const_var (nl "logical_and")
  , const_var (nl "logical_or")
  , const_var (nl "logical_xor")
  -- engines
  , const_var (nisa "unknown_engine")
  , const_var (nisa "tensor_engine")
  , const_var (nisa "vector_engine")
  , const_var (nisa "scalar_engine")
  , const_var (.str (nisa "reduce_cmd") "idle")
  , const_var (.str (nisa "reduce_cmd") "reset")
  , const_var (.str (nisa "reduce_cmd") "reduce")
  , const_var (.str (nisa "reduce_cmd") "reset_reduce")
  , (nl "mgrid", .mgrid)
  ]
  ++ NKIBuiltins.map fun (x,_) => (x, .builtin x (.obj x) none)
