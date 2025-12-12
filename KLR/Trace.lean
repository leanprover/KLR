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
import KLR.Trace.Builtin
import KLR.Trace.NKI
import KLR.Trace.Python
import KLR.Trace.Term
import KLR.Trace.Types

namespace KLR.Trace
open Compile.Pass (PassM)

-- Keywords recognized by the tracer (KLR keywords)
-- Limits come from:
-- https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/nki_arch_guides.html
def keywords : List (Name × Term) :=
  let ptr name memory parSize freeSize :=
    (name, Term.pointer { name := name.toString, memory, parSize, freeSize })
  [ ptr `hbm  .hbm  0xffffffff 0xffffffff -- TODO: size of HBM?
  , ptr `sbuf .sbuf 128 0x30000
  , ptr `psum .psum 128 0x4000
  ]

def globalEnv := keywords ++ builtinEnv ++ pythonEnv ++ NKIEnv

def kernelEnv (arch : Nat) : List (Name × Term) :=
  let base := [
    const_int (`arch) arch,
    const_int (.str (nl "tile_size") "pmax") 128,
    const_int (.str (nl "tile_size") "psum_fmax") 512,
    const_int (.str (nl "tile_size") "gemm_stationary_fmax") 128,
    const_int (.str (nl "tile_size") "gemm_moving_fmax") 512,
    const_int (.str (nl "tile_size") "bn_stats_fmax") 512,
    const_int (.str (nl "tile_size") "psum_min_align") 4,
    const_int (.str (nl "tile_size") "sbuf_min_align") 1,
    ]
  match arch with
  | 2 => base ++ [const_int (.str (nl "tile_size") "total_available_sbuf_size") 180224]
  | 3 => base ++ [const_int (.str (nl "tile_size") "total_available_sbuf_size") 212984]
  | 4 => base ++ [const_int (.str (nl "tile_size") "total_available_sbuf_size") 245752]
  | _ => []

def runNkiKernel
     (k : KLR.NKI.Kernel)
     (genDebug : Bool)
     (pid : Option (Nat × Nat))
     : PassM (TraceResult Core.Kernel) := do
  let int i := Term.int i
  let env := match pid with
    | none => (nl "_program_id", int 0) ::
              (nl "_num_programs", int 1) ::
              (nl "_program_ndim", int 0) :: kernelEnv k.arch ++ globalEnv
    | some (p,n) => (nl "_program_id", int p) ::
                    (nl "_num_programs", int n) ::
                    (nl "_program_ndim", int 1) :: kernelEnv k.arch ++ globalEnv
  tracer genDebug env (traceKernel k)

-- TODO: check that inputs and outputs are the same
-- TODO: check that shared constants are the same
-- TODO: check that schedule edges make sense
def runLncKernels (k : NKI.Kernel) (genDebug : Bool := false)
  : PassM (List (TraceResult Unit) × Core.LncKernel) := do
  let num := k.grid.max 1
  let res <- runNkiKernel k genDebug (0, num)
  let k0 := res.result
  let mut sharedBuffers : List (Core.TensorName × Pos) := res.sharedBuffers

  let dedupSharedBuf (tensors : List (Core.TensorName × Pos)) : PassM (List Core.TensorName) := do
    let grps := tensors.groupByKey (·.1.name)
    let results <- grps.toList.mapM fun (name, grp) => do
      if grp.length == 1 then
        match grp with
        | [single] =>
          withPos single.2 do
            warn s!"Tensor with name {name} is declared as shared but only appears in 1 lnc kernel. Consider explicit naming or marking buffer private_hbm"
          pure none
        | _ => throw "Unexpected group size"
      else match grp with
        | [] => throw "Empty tensor group"
        | first :: rest =>
          if rest.all (fun x => x.1.shape == first.1.shape && x.1.dtype == first.1.dtype)
          then pure (some first.1)
          else throw s!"Tensor {first.1.name} has mismatched shape or dtype across program instances"
    return results.filterMap id

  let mut result := [{ res with result := () }]
  let mut bodies := [res.result.body]
  for i in [1:num] do
    let res <- runNkiKernel k genDebug (i,num)
    result := { res with result := () } :: result
    bodies := res.result.body :: bodies
    sharedBuffers := sharedBuffers ++ res.sharedBuffers

  let kernel : Core.LncKernel := {
    name := k0.name
    inputs := k0.inputs
    outputs := k0.outputs
    bodies := bodies.reverse
    sharedConstants := []
    edges := k.edges
    sharedBuffers := <- if num > 1 then dedupSharedBuf sharedBuffers else pure (sharedBuffers.map (·.1))
  }
  return (result.reverse, kernel)
