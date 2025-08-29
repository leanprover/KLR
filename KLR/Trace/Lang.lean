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
import KLR.Trace.ISA
import KLR.Trace.Types

/-
NKI Language builtins
-/

namespace KLR.Trace
open Core

def langSyms := [
  -- datatypes
  "uint8", "int8", "uint16", "int16", "uint32", "int32",
  "float8e3", "float8e4", "float8e5",
  "float8_e4m3", "float8_e5m2",
  "float16", "bfloat16", "tfloat32", "float32",
  "bool_",
  -- buffer names
  "shared_hbm", "private_hbm", "hbm", "sbuf", "psum",
  -- activation function types
  "idle", "reset", "reduce", "reset_reduce",
  -- functions
  "invert", "bitwise_and", "bitwise_or", "bitwise_xor",
  "left_shift", "right_shift",
  "add", "subtract", "multiply", "maximum", "minimum",
  "equal", "not_equal", "greater_equal",
  "greater", "less_equal", "less",
  "logical_not", "logical_and", "logical_or", "logical_xor",
  -- activation functions
  "copy", "square", "sigmoid", "relu", "gelu", "gelu_dx", "gelu_apprx_tanh",
  "silu", "silu_dx", "tanh", "softplus", "mish", "erf", "erf_dx", "exp",
  "log", "sin", "arctan", "sqrt", "rsqrt", "reciprocal", "sign", "abs",
]

nki builtin.lang.ndarray
  (shape : Shape)
  (dtype : Dtype)
  (buffer : Option Memory := none)
  (name : Option String := none)
  (address : Option (Nat × Nat) := none) := do
    let memory := buffer.getD .sbuf
    let (parSize, freeSize) := Address.defaultSize shape dtype
    let (parOffset, freeOffset) := match address with
    | some (par, free) => (some par, some free)
    | none => (none, none)
    let name <- tensorName name
    let address := { name, memory, parSize, freeSize, parOffset, freeOffset : Address }
    let tensor <- TensorName.make name dtype shape address
    return .access (.simple tensor)

nki builtin.lang.par_dim (t : Term) := do
  warn "par_dim is deprecated"
  return t

nki builtin.lang.get_nc_version := do
  lookup `arch

nki builtin.lang.program_id (axis : Int) := do
  if axis != 0 then
    throw s!"invalid program axis {axis} (must be zero)"
  lookup (nl "_program_id")

nki builtin.lang.num_programs (axes : Option Int := none) := do
  if axes.getD 0 != 0 then
    throw s!"invalid program axis {axes} (must be zero)"
  lookup (nl "_num_programs")

nki builtin.lang.program_ndim := do
  lookup (nl "_program_ndim")

nki builtin.lang.ds (start : Int) (size : Int) := do
  return .mgItem start (start + size) 1

-- We can't change the variable names to add an "_" or the macros will
-- not resolve user parameters correctly.
-- TODO remove this setting one builtins are fully implemented (or removed)
set_option linter.unusedVariables false

nki builtin.lang.load
  (src : Access)
  (mask : Term := .none)
  (dtype : Option Dtype := none) := do
  warn "load is not supported"
  return .access src

nki builtin.lang.store (dst : Access) (src : Access) := do
  warn "store is not supported"
  return .none

nki builtin.lang.copy (src : Access) (dst : Access) := do
  warn "copy is not supported"
  return .none
