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
  [ const_int `arch 2
  , ptr `hbm  .hbm  0xffffffff 0xffffffff -- TODO: size of HBM?
  , ptr `sbuf .sbuf 128 0x30000
  , ptr `psum .psum 128 0x4000
  ]

def globalEnv := keywords ++ builtinEnv ++ pythonEnv ++ NKIEnv

def runNkiKernel
     (k : KLR.NKI.Kernel)
     (pid : Option (Nat × Nat) := none)
     : PassM (TraceResult Core.Kernel) := do
  let int i := Term.int i
  let env := match pid with
    | none => (nl "_program_id", int 0) ::
              (nl "_num_programs", int 1) ::
              (nl "_program_ndim", int 0) :: globalEnv
    | some (p,n) => (nl "_program_id", int p) ::
                    (nl "_num_programs", int n) ::
                    (nl "_program_ndim", int 1) :: globalEnv
  tracer env (traceKernel k)

-- TODO: check that inputs and outputs are the same
-- TODO: check that shared constants are the same
-- TODO: check that schedule edges make sense
def runLncKernels (k : NKI.Kernel) : PassM (List (TraceResult Unit) × Core.LncKernel) := do
  let num := k.grid.max 1
  let res <- runNkiKernel k (0, num)
  let k0 := res.result

  let mut result := [{ res with result := () }]
  let mut bodies := [res.result.body]
  for i in [1:num] do
    let res <- runNkiKernel k (i,num)
    result := { res with result := () } :: result
    bodies := res.result.body :: bodies

  let kernel : Core.LncKernel := {
    name := k0.name
    inputs := k0.inputs
    outputs := k0.outputs
    bodies := bodies.reverse
    sharedConstants := []
    edges := k.edges
  }
  return (result.reverse, kernel)
