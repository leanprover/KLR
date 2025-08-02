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

open Lean

abbrev typKind : SyntaxNodeKind := `typ

abbrev expKind : SyntaxNodeKind := `exp

abbrev stmtKind : SyntaxNodeKind := `stmt

abbrev stmtSeqKind : SyntaxNodeKind := `stmtSeq

abbrev defKind : SyntaxNodeKind := `def

def prattParserAntiquot (kind : Name) (name : String) (parsingTables : PrattParsingTables) : ParserFn :=
  prattParser kind parsingTables .default (mkAntiquot name kind false true).fn

def precCache (kind : Name) (pFn : ParserFn) (expected : List String) (prec : Nat) : Parser :=
  setExpected expected
    {fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn kind pFn)}

namespace Parse

  unsafe def pExp : Parser :=
    p 0
  where
    paren := leading_parser:maxPrec ("(" >> p 0 >> ")")

    num := numLit

    add := trailing_parser:30:30 (" + " >> p 31)
    mul := trailing_parser:35:35 (" * " >> p 36)

    parsingTables := {
      leadingTable := {
        (`«(», paren, maxPrec),
        (numLitKind, num, maxPrec)
      },
      trailingTable := {
        (`«+», add, 30),
        (`«*», mul, 35)
      },
    }
    pFn := prattParserAntiquot expKind "exp" parsingTables
    p := precCache expKind pFn ["expression"]

  mutual

  unsafe def pStmt : Parser :=
    p 0
  where
    exp := pExp

    dfn := pDef

    pass := leading_parser:maxPrec "pass"

    parsingTables := {
      leadingTable := {
        (`pass, pass, maxPrec),
        (`def, dfn, maxPrec)
      },
      leadingParsers := [
        (exp, maxPrec)
      ],
      trailingTable := {
      },
    }
    pFn := prattParserAntiquot stmtKind "stmt" parsingTables
    p := precCache stmtKind pFn ["statement"]

  unsafe def pStmtSeq : Parser := leading_parser
    sepBy1Indent pStmt "; " (allowTrailingSep := true)

  unsafe def pDef : Parser :=
    p 0
  where
    dfn := leading_parser:maxPrec
      -- Parser.optional Parser.checkWsBefore >> "def " >> identNoAntiquot >> "(" >> Parser.sepBy identNoAntiquot ", " >> ")" >> ":" >> pStmtSeq
      "def " >> identNoAntiquot >> "(" >> Parser.sepBy identNoAntiquot ", " >> ")" >> ":" >> {fn := whitespace} >> pStmtSeq
      -- "def " >> identNoAntiquot >> "(" >> Parser.sepBy identNoAntiquot ", " >> ")" >> ":" >> pStmtSeq

    parsingTables := {
      leadingTable := {
        (`def, dfn, maxPrec)
      }
    }
    pFn := prattParserAntiquot defKind "def" parsingTables
    p := precCache defKind pFn ["def"]

  end

  unsafe def pPy : Parser :=
    Parser.withPosition ({fn := whitespace} >> Parser.sepByIndent pStmt "; " (allowTrailingSep := true)) >> {fn := whitespace} >> Parser.eoi

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

  def throwUnsupportedSyntax {α} (pos : Pos) : EvalM α := do
    PassM.withPos pos do
      throw "unsupported syntax"

end EvalM

namespace Eval
  open Parse

  partial def eExp (stx : TSyntax expKind) : EvalM Exp := do
    let pos ← .getPos stx
    match stx with
    | `(pExp.paren| ($e:exp)) => eExp e
    | `(pExp.num| $n:num) => pure ⟨pos, .value <| .int <| n.getNat⟩
    | `(pExp| $x:exp * $y:exp) => do
      let x ← eExp x
      let y ← eExp y
      pure ⟨pos, .binOp .mul x y⟩
    | `(pExp| $x:exp + $y:exp) => do
      let x ← eExp x
      let y ← eExp y
      pure ⟨pos, .binOp .add x y⟩
    | _ => .throwUnsupportedSyntax pos

  partial def eStmt (stx : TSyntax stmtKind) : EvalM Stmt := do
    let pos ← .getPos stx
    match stx with
    | `(pStmt.pass| pass) => pure ⟨pos, .pass⟩
    | `(pStmt| $e:exp) => pure ⟨pos, .exp (← eExp e)⟩
    -- | _ => .throwUnsupportedSyntax pos

  def eStmtSeq (stx : TSyntax stmtSeqKind) : EvalM (List Stmt) :=
    dbg_trace stx
    return []

  def py (stx : Syntax) (fileMap : FileMap) : Except String (List Stmt) :=
    match ((eStmtSeq ⟨stx⟩).run { fileMap }).run {} with
    | .ok (stmts, _) _ => .ok stmts
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
  -- "\n",
  "(", ")",
  "+", "*",
  "def", ":", ";",
  "pass"
}

def runPyParser (source fileName : String) (fileMap : FileMap) : IO (Except String Syntax) := unsafe do
  let s ← runParser source fileName Parse.pPy pyTokens
  if s.hasError then
    let { line, column } := fileMap.toPosition s.pos
    return .error s!"{fileName} {line}:{column}: {s.errorMsg.get!.toString}"
  else
    return .ok s.stxStack.back

-- def evalPy (source fileName : String) : IO (Except String (List Stmt)) := do
--   let fileMap := source.toFileMap
--   let stx ←← runPyParser source fileName fileMap
--   return Eval.py stx fileMap

-- #eval runPyParser "pass" "<input>" "pass".toFileMap
def str :=
"
def fo():
  pass
"
-- "
-- # com1
-- def foo ()       : # com2
-- # com3
--   # com4
--   1 + 1
--   # com5
-- # com6

-- "
#eval return (←← runPyParser str "<input>" str.toFileMap).prettyPrint
-- #eval return (← evalPy "(42 + 1)" "<input>").map (Stmt.listReprPrec · 0)
-- #eval return (← evalPy "pass" "<input>").map (Stmt.listReprPrec · 0)
