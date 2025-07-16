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
open System Lake DSL

package FFIUtil

def noStackProtector := "-fno-stack-protector"

def moreWeakArgs :=
  if System.Platform.isOSX then #[] else #[noStackProtector]

target lean_util.o pkg : FilePath := do
  let oFile := pkg.buildDir / "lean_util.o"
  let srcJob ← inputTextFile <| pkg.dir / "lean_util.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ moreWeakArgs
  buildO oFile srcJob weakArgs #["-fPIC", "-Werror"] "cc" getLeanTrace

@[default_target]
extern_lib liblean_util pkg := do
  let ffiO ← lean_util.o.fetch
  let name := nameToSharedLib "lean_util"
  buildStaticLib (pkg.sharedLibDir / name) #[ffiO]
