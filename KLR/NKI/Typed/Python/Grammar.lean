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
import KLR.NKI.Typed.Python.Basic
import KLR.NKI.Typed.Python.Parser
-- import Lean
-- import Qq
-- import KLR.NKI.Typed.Common
-- import KLR.NKI.Typed.PIR

namespace KLR.NKI.Typed.Python.Parser

open KLR.Core (Pos)
open KLR.Compile.Pass (Pass PosError PassM)

open Lean Parser

abbrev expKind : SyntaxNodeKind := `exp
abbrev stmtKind : SyntaxNodeKind := `stmt
abbrev defKind : SyntaxNodeKind := `def

mutual

partial def expFn : ParserFn :=
  let add := trailing_parser:30:30 " + " >> expParser 31
  let mul := trailing_parser:35:35 " * " >> expParser 35
  let paren := leading_parser:maxPrec "(" >> expParser 0 >> ")"

  let parsingTables : PrattParsingTables := {
    leadingTable := {(numLitKind, numLit, maxPrec), (`«(», paren, maxPrec)},
    trailingTable := {(`«+», add, 30), (`«*», mul, 35)},
  }
  prattParser expKind parsingTables .default

partial def expParser (prec : Nat := 0) : Parser := leading_parser
  setExpected [ "expression" ]
    {fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn expKind expFn)}

partial def exp : Parser := leading_parser
  mkAntiquot "exp" expKind (isPseudoKind := true) <|>
    expParser

end

def pyTokens : TokenTable := {
  -- "$", ":",
  "(", ")",
  "+", "*"
}

def runPyParser (source fileName : String) : IO Unit := do
  let s ← runParser source fileName expParser pyTokens
  if s.hasError then
    let fileMap := source.toFileMap
    let { line, column } := fileMap.toPosition s.pos
    IO.println s!"error at {line}:{column}: {s.errorMsg.get!.toString}"
  else
    dbg_trace s.stxStack.back

#eval runPyParser "10 + 1" "<input>"

structure ExpandState where
  fileMap : FileMap

abbrev ExpandM := Pass ExpandState

def ExpandM.getPos (stx : Syntax) : ExpandM Pos := do
  let some info := stx.getInfo?
    | throw s!"cannot get source position for:\n{stx.prettyPrint}"
  let some startPos := info.getPos?
    | throw s!"cannot get starting source position for:\n{stx.prettyPrint}"
  let endPos := info.getTailPos?
  let { fileMap } ← get
  let { line, column } := fileMap.toPosition startPos
  match endPos with
  | some endPos =>
    let { line := lineEnd, column := columnEnd } := fileMap.toPosition endPos
    pure { line, column, lineEnd, columnEnd }
  | none => pure { line, column }

def throwUnsupportedSyntax (stx : Syntax) : ExpandM α := do
  PassM.withPos (← .getPos stx) do
    throw "unsupported syntax"

def expandExp : TSyntax `exp → ExpandM Exp
  --
  -- | `(exp| $e1:exp + $e2:exp) => sorry
  | stx => throwUnsupportedSyntax stx
