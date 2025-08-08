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

import Lean
import KLR.Core
namespace KLR.NKI.Typed.Python

open KLR.Core (Pos)
open Lean (FileMap)

class HasFileInfo (m : Type → Type) where
  fileName : m String
  fileMap  : m FileMap

def mkPos {m} [Monad m] [HasFileInfo m] (startPos endPos : String.Pos) : m Pos := do
  let fileMap ← HasFileInfo.fileMap
  let { line, column } := fileMap.toPosition startPos
  let { line := lineEnd, column := columnEnd } := fileMap.toPosition endPos
  pure { line, column, lineEnd, columnEnd }

def formatError {m} [Monad m] [HasFileInfo m] (pre : String) (msg : String) (startPos endPos : String.Pos) : m String := do
  let fileName ← HasFileInfo.fileName
  let fileMap  ← HasFileInfo.fileMap
  let { line, column } := fileMap.toPosition startPos
  let { line := lineEnd, column := columnEnd } := fileMap.toPosition endPos
  return s!"{pre} {fileName}:{line}:{column}-{lineEnd}:{columnEnd}: {msg}"
