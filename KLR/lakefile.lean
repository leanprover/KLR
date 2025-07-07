import Lake
open Lake DSL

package Util

@[default_target]
lean_lib Util

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.20.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.12"

require SHerLOC from git
  "https://github.com/leanprover/SHerLOC.git" @ "c74ae090d4326cca9ff636184c330a67ca039ef6"

-- Comment the above and uncomment this for local development
-- require TensorLib from "../../TensorLib"
