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

nki builtin.lang.ndarray
  (shape : Shape)
  (dtype : Dtype)
  (buffer : Option Memory := none)
  (name : Option String := none)
  (address : Option (Nat × Nat) := none)
  (address_rotation : Option Bool := none) := do
    let memory := buffer.getD .sbuf
    let (parSize, freeSize) := Address.defaultSize shape dtype
    let (parOffset, freeOffset) := match address with
    | some (par, free) => (some par, some free)
    | none => (none, none)
    let name <- tensorName name
    let address_rotation <- match address_rotation with
    | some v => pure v
    | none => flags.address_rotation
    let address := { name, memory, parSize, freeSize, parOffset, freeOffset : Address }
    let tensor <- TensorName.make name dtype shape address address_rotation
    return .access (.simple tensor)

nki builtin.lang.par_dim (t : Term) := do
  warn "par_dim is deprecated"
  return t

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
  return .slice start (start + size) (some 1)

nki builtin.lang.unique_name (name : String) := do
  let uniqueName := <- genName name.toName
  return .string uniqueName.toString

nki builtin.lang.random_seed
  (seed : Int)
  (name : Option String := none) := do
  Trace.add_stmt $ .oper (.randomSeed {
    seed := seed
  }) name
  return .none

nki builtin.lang.rand
  (dst : Access)
  (name : Option String := none) := do
  Trace.add_stmt $ .oper (.rand {
    dst := .abstract dst
  }) name
  return .none
