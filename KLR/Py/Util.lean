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

open Lean (ToJson FileMap)

deriving instance ToJson for String.Pos

namespace KLR.Py

structure Pos where
  pos     : String.Pos := {}
  stopPos : String.Pos := {}
deriving ToJson, Repr, Inhabited, BEq

structure FileInfo where
  content  : String
  fileMap  : FileMap
  fileName : String

def FileInfo.formatError (f : FileInfo) (pre : String) (msg : String) (pos : Pos) : String :=
  let fileMap := f.fileMap
  let input := f.content

  let { line, column } := fileMap.toPosition pos.pos
  let { line := lineEnd, column := columnEnd } := f.fileMap.toPosition (pos.stopPos)

  let startPos := fileMap.ofPosition { line := line, column := 0 }
  let endPos := fileMap.ofPosition { line := lineEnd + 1, column := 0 }
  let code := input.extract startPos endPos
  let lines := (code.split (· == '\n')).filter (not ∘ String.isEmpty)
  let markedLines : List String := (lines.zip (List.range lines.length)).map (
    fun (line, i) =>
      let markStart := if i == 0 then column else 0
      let markEnd := if i == lines.length - 1 then columnEnd else line.length
      let pre := "".pushn ' ' markStart
      let mark := "".pushn '^' (markEnd - markStart)
      line ++ "\n" ++ pre ++ mark
  )
  let markedCode := Std.Format.nest 2 ("\n" ++ Std.Format.joinSep markedLines "\n")

  let posMsg := s!"{pre}: {f.fileName}:{line}:{column + 1}:"
  let errMsg := s!"{msg}"
  s!"{posMsg}{markedCode}\n{errMsg}"

namespace _Debug

def input := "1
23456
  79
  a
  80000
bcd"
def pos : Pos := ⟨input.find (· == '3'), input.next <| input.find (· == '8')⟩
def info : FileInfo := ⟨input, input.toFileMap, "/usr/code/my.py"⟩
def err := info.formatError "SyntaxError" "invalid syntax" pos

/--
info: SyntaxError: /usr/code/my.py:2:2:
  23456
   ^^^^
    79
  ^^^^
    a
  ^^^
    80000
  ^^^
invalid syntax
-/
#guard_msgs in #eval IO.println err

end _Debug
