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

import Lake
open Lake DSL

package Util

@[default_target]
lean_lib Util

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.21.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.12"

-- Comment the above and uncomment this for local development
-- require TensorLib from "../../TensorLib"
