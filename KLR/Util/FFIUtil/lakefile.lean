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
