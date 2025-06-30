import Lake
open Lake DSL

package Util

@[default_target]
lean_lib Util

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.20.0"

require TensorLib from git
  "https://github.com/leanprover/TensorLib.git" @ "v0.0.10"

require iris from git
  "https://github.com/markusdemedeiros/iris-lean.git"
