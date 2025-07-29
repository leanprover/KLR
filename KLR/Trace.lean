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
  let ptr s memory size :=
    (Lean.Name.mkStr1 s, Term.pointer { memory, parSize := size.1, freeSize := size.2 })
  let const s := const_var (.mkStr1 s)
  let int s := const_int (.mkStr1 s)
  [ int "arch" 2
  , ptr "hbm"  .hbm  (0xffffffff, 0xffffffff) -- TODO: size of HBM?
  , ptr "sbuf" .sbuf (128, 0x30000)
  , ptr "psum" .psum (128, 0x4000)
  , const "range"
  ]

def globalEnv := keywords ++ NKIEnv ++ NumpyEnv

def runNKIKernel (k : KLR.NKI.Kernel) : Err (String × KLR.Core.Kernel) :=
  tracer globalEnv (traceKernel k)
