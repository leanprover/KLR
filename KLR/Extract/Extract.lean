/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import Extract.C
import Extract.Python
import Extract.Serde
import Extract.ToPython
import Lean

namespace Extract
open Lean Meta

private def withFile (file : String) (m : MetaM Unit) : MetaM Unit := do
  let h <- IO.FS.Handle.mk file IO.FS.Mode.write
  IO.withStdout (.ofHandle h) m

private def dir := "../../interop/klr"

run_meta do
  withFile s!"{dir}/ast_common.h" C.generateCommonAST
  withFile s!"{dir}/ast_python_core.h" C.generatePythonAST
  --withFile s!"{dir}/ast_python_core.py" Python.generatePythonAST
  withFile s!"{dir}/ast_nki.h" C.generateNkiAST
  withFile s!"{dir}/ast_nki.py" Python.generateNkiAST
  withFile s!"{dir}/serde_common.h" Serde.generateCommonH
  withFile s!"{dir}/serde_common.c" Serde.generateCommonC
  withFile s!"{dir}/serde_python_core.h" Serde.generatePythonH
  withFile s!"{dir}/serde_python_core.c" Serde.generatePythonC
  withFile s!"{dir}/serde_nki.h" Serde.generateNkiH
  withFile s!"{dir}/serde_nki.c" Serde.generateNkiC
  withFile s!"{dir}/topy_nki.h" ToPython.generateNkiH
  withFile s!"{dir}/topy_nki.c" ToPython.generateNkiC
