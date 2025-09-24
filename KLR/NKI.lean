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

import KLR.Compile.Pass
import KLR.NKI.Annotations
import KLR.NKI.Basic
import KLR.NKI.Classes
import KLR.NKI.Patterns
import KLR.NKI.Pretty
import KLR.NKI.Simplify
import KLR.NKI.SimplifyOperators
--import KLR.NKI.Typed

namespace KLR.NKI
open Compile.Pass (PassM runPass)

def compile (py : Python.Kernel) : PassM NKI.Kernel := do
  let k <- runPass (simplify py)
  let k <- runPass (simplifyOperators k)
  let k <- runPass (annotate k)
  let k <- runPass (simplifyPatterns k)
  let k <- runPass (genClasses k)
  return k
