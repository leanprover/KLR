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

open Lean

/-!
https://docs.python.org/3/reference/grammar.html
-/

abbrev typKind : SyntaxNodeKind := `typ

abbrev expKind : SyntaxNodeKind := `exp

abbrev stmtKind : SyntaxNodeKind := `stmt

abbrev stmtsKind : SyntaxNodeKind := `stmts

abbrev simplStmtsKind : SyntaxNodeKind := `simplStmts

abbrev compndStmtKind : SyntaxNodeKind := `compndStmt

abbrev blockKind : SyntaxNodeKind := `block

abbrev defKind : SyntaxNodeKind := `def

def prattParserAntiquot (kind : Name) (name : String) (parsingTables : PrattParsingTables) : ParserFn :=
  prattParser kind parsingTables .default (mkAntiquot name kind false true).fn

def precCache (kind : Name) (pFn : ParserFn) (expected : List String) (prec : Nat) : Parser :=
  setExpected expected
    {fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn kind pFn)}

-- @[builtin_doc, inline] def sepBy1Indent (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
--   let p := Parser.withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
--   Parser.withPosition <|
--     Parser.sepBy1
--       (Parser.checkColGe >> p)
--       sep
--       (psep <|> Parser.checkColEq >> Parser.checkLinebreakBefore >> Parser.pushNone)
--       allowTrailingSep

namespace Parse

  unsafe def pTyp : Parser :=
    p
  where
    id    := Parser.ident
    none  := leading_parser:maxPrec "None"
    bool  := leading_parser:maxPrec "bool"
    int   := leading_parser:maxPrec "int"
    float := leading_parser:maxPrec "float"
    str   := leading_parser:maxPrec "str"
    tuple := leading_parser:maxPrec
      "tuple" >> "[" >> Parser.sepBy1 p ", " (allowTrailingSep := true) >> "]"
    list  := leading_parser:maxPrec "list" >> "[" >> p >> "]"
    func  := leading_parser:maxPrec
      "FunctionType" >> "[" >> Parser.sepBy1 p ", " (allowTrailingSep := true) >> "]"

    parsingTables := {
      leadingTable := {
        (identKind, id, maxPrec),
        (`None, none, maxPrec),
        (`bool, bool, maxPrec),
        (`int, int, maxPrec),
        (`float, float, maxPrec),
        (`str, str, maxPrec),
        (`tuple, tuple, maxPrec),
        (`list, list, maxPrec),
        (`FunctionType, func, maxPrec)
      },
      leadingParsers := [
      ],
      trailingTable := {
      },
    }
    pFn := prattParserAntiquot typKind "typ" parsingTables
    p (prec : Nat := 0) := precCache typKind pFn ["type"] prec

  /--
  Refer to this doc for operator precedence:
  https://docs.python.org/3/reference/expressions.html#operator-precedence
  -/
  unsafe def pExp : Parser :=
    p
  where
    paren      := leading_parser:maxPrec "(" >> p >> ")"
    id         := Parser.ident
    -- Atoms
    none       := leading_parser:maxPrec "None"
    tt         := leading_parser:maxPrec "True"
    ff         := leading_parser:maxPrec "False"
    num        := Parser.numLit
    scientific := Parser.scientificLit
    str        := Parser.strLit
    -- Operations
    pow        := trailing_parser:100:101 " ** " >> p 100
    neg        := leading_parser:95 "-" >> p 95
    mul        := trailing_parser:90:90 " * " >> p 91
    div        := trailing_parser:90:90 " / " >> p 91
    floor      := trailing_parser:90:90 " // " >> p 91
    mod        := trailing_parser:90:90 " % " >> p 91
    add        := trailing_parser:85:85 " + " >> p 86
    sub        := trailing_parser:85:85 " - " >> p 86
    /-
    NOTE: Chaining of comparisons is disallowed.
    Python expands `a < b < c` to `a < b and b < c`,
    while `a < (b < c)` compares `a` to the boolean result of `b < c`.
    This is confusing, so we force chained comparisons to be expanded manually,
    while `a < (b < c)` is a type error.
    -/
    ge         := trailing_parser:80:81 " >= " >> p 81
    gt         := trailing_parser:80:81 " > " >> p 81
    le         := trailing_parser:80:81 " <= " >> p 81
    lt         := trailing_parser:80:81 " < " >> p 81
    ne         := trailing_parser:80:81 " != " >> p 81
    eq         := trailing_parser:80:81 " == " >> p 81
    land       := trailing_parser:75:75 " and " >> p 76
    lor        := trailing_parser:70:70 " or " >> p 71
    -- TODO: check precedence here
    ite        := trailing_parser:65 " if " >> p 67 >> " else " >> p 66
    tuple      := leading_parser:maxPrec
      "(" >> p >> "," >> Parser.sepBy p ", " (allowTrailingSep := true) >> ")"
    list       := leading_parser:maxPrec "[" >> Parser.sepBy p ", " (allowTrailingSep := true) >> "]"
    arg        := withAntiquot (mkAntiquot "arg" `arg) <|
      leading_parser:maxPrec Parser.optional (Parser.ident >> "=") >> p
    -- TODO: check precedence here
    call       := trailing_parser:110:110
      Parser.optional ("[" >> Parser.sepBy1 pTyp ", " (allowTrailingSep := true) >> "]") >>
        "(" >> Parser.sepBy arg ", " (allowTrailingSep := true) >> ")"
    attr       := trailing_parser:110:110 "." >> Parser.ident

    parsingTables := {
      leadingTable := {
        (`«(», paren, maxPrec),
        (identKind, id, maxPrec),
        (`None, none, maxPrec),
        (`True, tt, maxPrec),
        (`False, ff, maxPrec),
        (numLitKind, num, maxPrec),
        (scientificLitKind, scientific, maxPrec),
        (strLitKind, str, maxPrec),
        (`«-», neg, 95),
        (`«(», tuple, maxPrec),
        (`«[», list, maxPrec)
      },
      trailingTable := {
        (`«**», pow, 100),
        (`«*», mul, 90),
        (`«/», div, 90),
        (`«//», floor, 90),
        (`«%», mod, 90),
        (`«+», add, 85),
        (`«-», sub, 85),
        (`«>=», ge, 80),
        (`«>», gt, 80),
        (`«<=», le, 80),
        (`«<», lt, 80),
        (`«!=», ne, 80),
        (`«==», eq, 80),
        (`and, land, 75),
        (`or, lor, 70),
        (`if, ite, 65),
        (`«[», call, 110),
        (`«(», call, 110),
        (`«.», attr, 110)
      },
    }
    pFn := prattParserAntiquot expKind "exp" parsingTables
    p (prec : Nat := 0) := precCache expKind pFn ["expression"] prec

  unsafe def pStmt : Parser :=
    p 0
  where
    exp := pExp

    -- dfn := pDef

    pass := leading_parser:maxPrec "pass"

    parsingTables := {
      leadingTable := {
        (`pass, pass, maxPrec)
        -- (`def, dfn, maxPrec)
      },
      leadingParsers := [
        (exp, maxPrec)
      ],
      trailingTable := {
      },
    }
    pFn := prattParserAntiquot stmtKind "stmt" parsingTables
    p := precCache stmtKind pFn ["statement"]

  -- unsafe def pStmtSeq : Parser := leading_parser
  --   sepBy1Indent pStmt "; " (psep := Parser.notFollowedBy "; " "def") (allowTrailingSep := true)

  -- unsafe def pDef : Parser :=
  --   p 0
  -- where
  --   dfn := leading_parser:maxPrec
  --     ("def " >> identNoAntiquot >>
  --       "(" >> Parser.sepBy identNoAntiquot ", " >> ")" >> ":" >>
  --      Parser.checkColGt >> pStmtSeq)

  --   parsingTables := {
  --     leadingTable := {
  --       (`def, dfn, maxPrec)
  --     }
  --   }
  --   pFn := prattParserAntiquot defKind "def" parsingTables
  --   p := precCache defKind pFn ["def"]

  -- unsafe def pPy : Parser :=
  --   Parser.sepByIndent pStmt "; " (allowTrailingSep := true) >> Parser.eoi

end Parse

open KLR.Core (Pos)
open KLR.Compile.Pass (Pass PosError PassM)

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

  def throwAt {α} (pos : Pos) (msg : String) : EvalM α := do
    PassM.withPos pos do
      throw msg

end EvalM

namespace Eval
  open Parse

  partial def eTyp (stx : TSyntax typKind) : EvalM Typ := do
    let pos ← .getPos stx
    let typ : Typ' ←
      match stx with
      | `(pTyp.id| $id:ident) => pure <| .var id.getId.toString
      | `(pTyp.none| None) => pure <| .prim .none
      | `(pTyp.bool| bool) => pure <| .prim .bool
      | `(pTyp.int| int) => pure <| .prim <| .numeric .int
      | `(pTyp.float| float) => pure <| .prim <| .numeric .float
      | `(pTyp.str| str) => pure <| .prim .string
      | `(pTyp.tuple| tuple[ $[$ts:typ],* ]) => do
        let ts ← ts.mapM eTyp
        pure <| .tuple ts.toList
      | `(pTyp.list| list[ $t:typ ]) => do
        let t ← eTyp t
        pure <| .list t
      | `(pTyp.func| FunctionType[ $[$ts:typ],* ]) => do
        let ts ← ts.mapM eTyp
        pure <| .func [] ts.toList
      | _ => .throwUnsupportedSyntax pos
    pure ⟨pos, typ⟩

  mutual

  partial def eArgs (pos : Pos) (args : Array (TSyntax `arg)) : EvalM (Array Arg) := do
    let args ← args.mapM (fun arg =>
      match arg with
      | `(pExp.arg| $[$id:ident =]? $e:exp) => do
        pure ⟨id.map (Name.toString ∘ TSyntax.getId), ← eExp e⟩
      | _ => .throwUnsupportedSyntax pos
    )
    .pure args

  partial def eExp (stx : TSyntax expKind) : EvalM Exp := do
    let pos ← .getPos stx
    match stx with
    -- paren      := leading_parser:maxPrec "(" >> p >> ")"
    | `(pExp.paren| ($e:exp)) => eExp e
    -- id         := Parser.ident
    | `(pExp.id| $id:ident) => pure ⟨pos, .var id.getId.toString⟩
    -- none       := leading_parser:maxPrec "None"
    | `(pExp.none| None) => pure ⟨pos, .value .none⟩
    -- tt         := leading_parser:maxPrec "True"
    | `(pExp.tt| True) => pure ⟨pos, .value <| .bool true⟩
    -- ff         := leading_parser:maxPrec "False"
    | `(pExp.ff| False) => pure ⟨pos, .value <| .bool false⟩
    -- num        := Parser.numLit
    | `(pExp.num| $n:num) => pure ⟨pos, .value <| .int <| n.getNat⟩
    -- scientific := Parser.scientificLit
    | `(pExp.scientific| $n:scientific) =>
      -- See: `Lean.TSyntax.getScientific`
      match n.getScientific with
      | (0, false, 0) => .throwAt pos "malformed float literal"
      | (n, sign, e) =>
        let f := if sign then n.toFloat * 10 ^ (-e.toFloat) else n.toFloat * 10 ^ e.toFloat
        pure ⟨pos, .value <| .float f⟩
    -- str        := Parser.strLit
    | `(pExp.str| $s:str) => pure ⟨pos, .value <| .string s.getString⟩
    -- pow        := trailing_parser:100:101 " ** " >> p 100
    -- | `(pExp| $b:exp ** $e:exp) => sorry
    -- neg        := leading_parser:95 "-" >> p 95
    | `(pExp.neg| -$e:exp) => do pure ⟨pos, .unaryOp .neg (← eExp e)⟩
    -- mul        := trailing_parser:90:90 " * " >> p 91
    | `(pExp| $x:exp * $y:exp) => do pure ⟨pos, .binOp .mul (← eExp x) (← eExp y)⟩
    -- div        := trailing_parser:90:90 " / " >> p 91
    | `(pExp| $x:exp / $y:exp) => do pure ⟨pos, .binOp .div (← eExp x) (← eExp y)⟩
    -- floor      := trailing_parser:90:90 " // " >> p 91
    | `(pExp| $x:exp // $y:exp) => do pure ⟨pos, .binOp .floor (← eExp x) (← eExp y)⟩
    -- mod        := trailing_parser:90:90 " % " >> p 91
    | `(pExp| $x:exp % $y:exp) => do pure ⟨pos, .binOp .mod (← eExp x) (← eExp y)⟩
    -- add        := trailing_parser:85:85 " + " >> p 86
    | `(pExp| $x:exp + $y:exp) => do pure ⟨pos, .binOp .add (← eExp x) (← eExp y)⟩
    -- sub        := trailing_parser:85:85 " - " >> p 86
    | `(pExp| $x:exp - $y:exp) => do pure ⟨pos, .binOp .sub (← eExp x) (← eExp y)⟩
    -- ge         := trailing_parser:80:80 " >= " >> p 80
    | `(pExp| $x:exp >= $y:exp) => do pure ⟨pos, .binOp .ge (← eExp x) (← eExp y)⟩
    -- gt         := trailing_parser:80:80 " > " >> p 80
    | `(pExp| $x:exp > $y:exp) => do pure ⟨pos, .binOp .gt (← eExp x) (← eExp y)⟩
    -- le         := trailing_parser:80:80 " <= " >> p 80
    | `(pExp| $x:exp <= $y:exp) => do pure ⟨pos, .binOp .le (← eExp x) (← eExp y)⟩
    -- lt         := trailing_parser:80:80 " < " >> p 80
    | `(pExp| $x:exp < $y:exp) => do pure ⟨pos, .binOp .lt (← eExp x) (← eExp y)⟩
    -- ne         := trailing_parser:80:80 " != " >> p 80
    | `(pExp| $x:exp != $y:exp) => do pure ⟨pos, .binOp .ne (← eExp x) (← eExp y)⟩
    -- eq         := trailing_parser:80:80 " == " >> p 80
    | `(pExp| $x:exp == $y:exp) => do pure ⟨pos, .binOp .eq (← eExp x) (← eExp y)⟩
    -- land       := trailing_parser:75:75 " and " >> p 76
    -- | `(pExp| $x:exp and $y:exp) => do pure ⟨pos, .binOp .land (← eExp x) (← eExp y)⟩
    -- lor        := trailing_parser:70:70 " or " >> p 71
    -- | `(pExp| $x:exp (or $y:exp)) => do pure ⟨pos, .binOp .lor (← eExp x) (← eExp y)⟩
    -- ite        := trailing_parser:65 " if " >> p 67 >> " else " >> p 66
    | `(pExp| $thn:exp if $cond:exp else $els:exp) => do pure ⟨pos, .ifExp (← eExp cond) (← eExp thn) (← eExp els)⟩
    -- tuple      := leading_parser:maxPrec "(" >> p >> "," >> Parser.sepBy p ", " >> Parser.optional "," >> ")"
    | `(pExp.tuple| ($fst:exp, $[$rest:exp],*)) => do
      let fst ← eExp fst
      let rest ← rest.mapM eExp
      pure ⟨pos, .tuple (fst :: rest.toList)⟩
    | `(pExp.list| [$[$es:exp],*]) => do
      let es ← es.mapM eExp
      pure ⟨pos, .list es.toList⟩
    | `(pExp| $f:exp ( $[$args:arg],* )) => do
      let f ← eExp f
      let args ← eArgs pos args
      pure ⟨pos, .call f [] args.toList⟩
    | `(pExp| $f:exp [ $[$typArgs:typ],* ] ( $[$args:arg],* )) => do
      dbg_trace "matched"
      let f ← eExp f
      let typArgs ← typArgs.mapM eTyp
      let args ← eArgs pos args
      pure ⟨pos, .call f typArgs.toList args.toList⟩
    | `(pExp| $e:exp.$f:ident) => do
      let e ← eExp e
      let f := f.getId.toString
      pure ⟨pos, .attr e f⟩
    | _ => .throwUnsupportedSyntax pos

  end

  partial def eStmt (stx : TSyntax stmtKind) : EvalM Stmt := do
    let pos ← .getPos stx
    match stx with
    | `(pStmt.pass| pass) => pure ⟨pos, .pass⟩
    | `(pStmt| $e:exp) => pure ⟨pos, .exp (← eExp e)⟩
    -- | _ => .throwUnsupportedSyntax pos

  def eStmtSeq (stx : TSyntax stmtSeqKind) : EvalM (List Stmt) :=
    dbg_trace stx
    return []

  -- def py (stx : Syntax) (fileMap : FileMap) : Except String (List Stmt) :=
  --   match ((eStmtSeq ⟨stx⟩).run { fileMap }).run {} with
  --   | .ok (stmts, _) _ => .ok stmts
  --   | .error err _ => .error err.msg

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
  /-
  Special characters
  Note that `"` and `'` are not included since string literal is a special token.
  -/
  "(", ")", "[", "]", ",", ":", ";", ".",
  /- Types -/
  "None", "bool", "int", "float", "tuple", "list", "FunctionType",
  /- Atoms -/
  "True", "False",
  /- Operators -/
  "**", "*", "/", "//", "%", "+", "-", ">=", ">", "<=", "<", "!=", "==",
  /- Keywords -/
  "if", "else", "def", "pass"
}

def runPyParser (source fileName : String) (fileMap : FileMap) : IO (Except String Syntax) := unsafe do
  let s ← runParser source fileName (Parse.pExp >> Parser.eoi) pyTokens
  if s.hasError then
    let { line, column } := fileMap.toPosition s.pos
    return .error s!"{fileName} {line}:{column}: {s.errorMsg.get!.toString}"
  else
    return .ok s.stxStack.back

def evalPy (source fileName : String) : IO (Except String Exp) := do
  let fileMap := source.toFileMap
  let stx ←← runPyParser source fileName fileMap
  match ((Eval.eExp ⟨stx⟩).run { fileMap }).run {} with
  | .ok (res, _) _ => return .ok res
  | .error err _ => return .error err.msg

def str := "foo(1, 2)"
#eval (evalPy str "<input>")
#eval return dbg_trace (←← runPyParser str "<input>" str.toFileMap); 0
-- #eval (evalPy str "<input>") >>= fun x =>
--   match x with
--   | .ok x => IO.println (toJson x).pretty
--   | .error err => IO.println s!"error: {err}"
