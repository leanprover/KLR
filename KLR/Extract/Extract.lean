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

import Extract.Basic
import Extract.C
import Extract.Cpp
import Extract.Python
import Extract.Serde
import Extract.SerdeCpp
import Extract.ToPython
import Lean

namespace Extract
open Lean Meta

private def withFile (file : String) (m : MetaM Unit) : MetaM Unit := do
  let h <- IO.FS.Handle.mk file IO.FS.Mode.write
  IO.withStdout (.ofHandle h) m

private def dir := "../../interop/klr"

-- Note: please leave commmented out items as we may need to bring these
-- back in follow-up commits.
run_meta do
  withFile s!"{dir}/ast_common.h" C.generateCommonAST
  withFile s!"{dir}/ast_file.h" C.generateFileAST
  withFile s!"{dir}/ast_python_core.h" C.generatePythonAST
  --withFile s!"{dir}/ast_nki.h" C.generateNkiAST
  --withFile s!"{dir}/ast_nki.py" Python.generateNkiAST
  --withFile s!"{dir}/ast_klir.h" C.generateKlrAST
  withFile s!"{dir}/serde_common.h" Serde.generateCommonH
  withFile s!"{dir}/serde_common.c" Serde.generateCommonC
  withFile s!"{dir}/serde_file.h" Serde.generateFileH
  withFile s!"{dir}/serde_file.c" Serde.generateFileC
  withFile s!"{dir}/serde_python_core.h" Serde.generatePythonH
  withFile s!"{dir}/serde_python_core.c" Serde.generatePythonC
  ---withFile s!"{dir}/serde_nki.h" Serde.generateNkiH
  ---withFile s!"{dir}/serde_nki.c" Serde.generateNkiC
  ---withFile s!"{dir}/serde_klir.h" Serde.generateKlrH
  ---withFile s!"{dir}/serde_klir.c" Serde.generateKlrC
  --withFile s!"{dir}/topy_nki.h" ToPython.generateNkiH
  --withFile s!"{dir}/topy_nki.c" ToPython.generateNkiC
  -- C++
  withFile s!"{dir}/klir_ast.hpp" Cpp.generateKlrAST
  withFile s!"{dir}/klir_serde.hpp" SerdeCpp.generateKlrH
  withFile s!"{dir}/klir_serde.cpp" SerdeCpp.generateKlrC
