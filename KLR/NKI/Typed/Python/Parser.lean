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
import KLR.NKI.Typed.Python.ParserUtil
import KLR.NKI.Typed.Python.PrettyPrint

namespace KLR.NKI.Typed.Python.Parser

open KLR.Core (Pos)
open KLR.Compile.Pass (Pass PosError PassM)

open Lean Parser

abbrev typKind : SyntaxNodeKind := `typ

abbrev expKind : SyntaxNodeKind := `exp

abbrev stmtKind : SyntaxNodeKind := `stmt

abbrev defKind : SyntaxNodeKind := `def

namespace Parse

unsafe def pExp : Parser :=
  p 0
where
  num := numLit
  paren := leading_parser:maxPrec ("(" >> p 0 >> ")")
  add := trailing_parser:30:30 (" + " >> p 31)
  mul := trailing_parser:35:35 (" * " >> p 36)
  pFn :=
    let parsingTables : PrattParsingTables := {
      leadingTable := {
        (`«$», num, maxPrec), -- needed for antiquot
        (`num, num, maxPrec),
        (`«(», paren, maxPrec)
      },
      trailingTable := {
        (`«+», add, 30),
        (`«*», mul, 35)
      },
    }
    prattParser expKind parsingTables .default (mkAntiquot "exp" expKind false true).fn
  p (prec : Nat) :=
    setExpected ["expression"]
      {fn := adaptCacheableContextFn ({ · with prec })
        (withCacheFn expKind pFn)}

end Parse

structure EvalState where
  fileMap : FileMap

abbrev EvalM := Pass EvalState

namespace EvalM

  def getPos (stx : Syntax) : EvalM Pos := do
    let some startPos := stx.getPos?
      | throw s!"cannot get starting source position for:\n{stx.prettyPrint}"
    let endPos := stx.getTailPos?
    let { fileMap } ← get
    let { line, column } := fileMap.toPosition startPos
    match endPos with
    | some endPos =>
      let { line := lineEnd, column := columnEnd } := fileMap.toPosition endPos
      pure { line, column, lineEnd, columnEnd }
    | none => pure { line, column }

  def throwUnsupportedSyntax {α} (stx : Syntax) : EvalM α := do
    PassM.withPos (← .getPos stx) do
      throw "unsupported syntax"

end EvalM

namespace Eval
  open Parse

  partial def eExp (stx : TSyntax expKind) : EvalM Exp := do
    let pos ← .getPos stx
    match stx with
    | `(pExp| $n:num) => pure ⟨pos, .value <| .int <| .ofNat n.getNat⟩
    | `(pExp| $x:exp * $y:exp) => do
      let x ← eExp x
      let y ← eExp y
      pure ⟨pos, .binOp .mul x y⟩
    | `(pExp| $x:exp + $y:exp) => do
      let x ← eExp x
      let y ← eExp y
      pure ⟨pos, .binOp .add x y⟩
    | stx =>
      .throwUnsupportedSyntax stx

  def py (stx : Syntax) (fileMap : FileMap) : Except String Exp :=
    match ((eExp ⟨stx⟩).run { fileMap }).run {} with
    | .ok (eExp, _) _ => .ok eExp
    | .error err _ => .error err.msg

end Eval

/--
TokenTable for Python.

Note: The antiquot parsers used to match on `Syntax` in Lean is also built-in to the
same parsers used to parse regular Python files. Here, the intentional omission of the `$`
token used to denote antiquotations means we will disallow antiquotations when parsing
a python file supplied by the user. This is fine because:
1. `$` has no special meaning in Python, so we don't need any parsing rules containing `$` tokens.
2. Even if we somehow parsed an antiquot, the `expandX` functions will throw an unsupported
   syntax when encoutering them.
-/
def pyTokens : TokenTable := {
  "(", ")",
  "+", "*"
}

def runPyParser (source fileName : String) (fileMap : FileMap) : IO (Except String Syntax) := unsafe do
  let s ← runParser source fileName Parse.pExp pyTokens
  if s.hasError then
    let { line, column } := fileMap.toPosition s.pos
    return .error s!"{fileName} {line}:{column}: {s.errorMsg.get!.toString}"
  else
    return .ok s.stxStack.back

def evalPy (source fileName : String) : IO (Except String Exp) := do
  let fileMap := source.toFileMap
  let stx ←← runPyParser source fileName fileMap
  return Eval.py stx fileMap

#eval return (← evalPy "100 * 10" "<input>").map (fun e => Exp.reprPrec e 0)
