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
import KLR.Trace.Numpy
import KLR.Trace.Term
import KLR.Trace.Types

namespace KLR.Trace

-- Keywords recognized by the tracer (KLR keywords)
-- Limits come from:
-- https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/nki_arch_guides.html
def keywords : List (Name × Term) :=
  let ptr name memory parSize freeSize :=
    (name, Term.pointer { memory, parSize, freeSize })
  [ const_int `arch 2
  , ptr `hbm  .hbm  0xffffffff 0xffffffff -- TODO: size of HBM?
  , ptr `sbuf .sbuf 128 0x30000
  , ptr `psum .psum 128 0x4000
  ]

def globalEnv := keywords ++ NKIEnv ++ NumpyEnv

def runNkiKernel (k : KLR.NKI.Kernel) (pid : Nat := 1) : Err (String × KLR.Core.Kernel) := do
  let pid := Term.expr (.value (.int pid)) .int
  let env := (nl "program_id", pid) :: globalEnv
  tracer env (traceKernel k)

-- TODO: probably the messages are identical, but they might not be
-- TODO: check that inputs and outputs are the same
def runLncKernels (k : KLR.NKI.Kernel) : Err (String × KLR.Core.LncKernel) := do
  let (m0, k0) <- runNkiKernel k 0
  let kernel : Core.LncKernel := {
    name := k0.name
    inputs := k0.inputs
    outputs := k0.outputs
    bodies := []
  }
  let mut msgs := [m0]
  let mut bodies := [k0.body]
  for i in [1:k.grid.max 1] do
    let (msg, k) <- runNkiKernel k i
    msgs := msg :: msgs
    bodies := k.body :: bodies
  let msg := "\n".intercalate msgs.reverse
  let kernel := { kernel with bodies := bodies.reverse }
  return (msg, kernel)
