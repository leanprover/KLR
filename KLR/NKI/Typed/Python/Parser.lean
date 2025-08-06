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

abbrev argKind : SyntaxNodeKind := `arg

abbrev idxKind: SyntaxNodeKind := `idx

abbrev expsKind : SyntaxNodeKind := `exps

abbrev patKind : SyntaxNodeKind := `pat

abbrev dottedNameKind : SyntaxNodeKind := `dottedName

abbrev stmtKind : SyntaxNodeKind := `stmt

abbrev stmtsKind : SyntaxNodeKind := `stmts

abbrev simplStmtKind : SyntaxNodeKind := `simplStmt

abbrev simplStmtsKind : SyntaxNodeKind := `simplStmts

abbrev compndStmtKind : SyntaxNodeKind := `compndStmt

abbrev blockKind : SyntaxNodeKind := `block

abbrev defKind : SyntaxNodeKind := `def

def prattParserAntiquot (kind : Name) (name : String) (parsingTables : PrattParsingTables) : ParserFn :=
  prattParser kind parsingTables .default (mkAntiquot name kind false true).fn

def precCache (kind : Name) (pFn : ParserFn) (expected : List String) (tokens : List Token) (prec : Nat) : Parser :=
  setExpected expected {
    fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn kind pFn),
    info := {
      collectTokens tokens' :=
        tokens.foldl (fun tk s => tk.insert s) tokens'
    }
  }

namespace Parse

  def typTokens : List Token := [
    "None", "bool", "int", "float", "str", "tuple", "list", "FunctionType", "[", "]"
  ]

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
        (`«$», id, maxPrec),
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
    p (prec : Nat := 0) := precCache typKind pFn ["type"] typTokens prec

  def expTokens : List Token := [
    "(", ")", "[", "]", ",", "=", ".",
    "None", "True", "False",
    "**", "*", "/", "//", "%", "+", "-",
    ">=", ">", "<=", "<", "!=", "==",
    "and", "or",
    "if", "else",
  ]

  def idxTokens : List Token := ["...", ":"]

  mutual

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
    arg        := leading_parser:maxPrec Parser.optional (Parser.ident >> "=") >> p
    -- TODO: check precedence here
    call       := trailing_parser:110:110
      Parser.optional ("[" >> setExpected ["type"] (Parser.sepBy1 pTyp ", " (allowTrailingSep := true)) >> "]") >>
        "(" >> Parser.sepBy arg ", " (allowTrailingSep := true) >> ")"
    attr       := trailing_parser:110:110 "." >> Parser.ident
    access     := trailing_parser:110:110 "[" >> Parser.sepBy1 pIdx "," (allowTrailingSep := true) >> "]"

    parsingTables := {
      leadingTable := {
        (`«(», paren, maxPrec),
        (identKind, id, maxPrec),
        (`«$», id, maxPrec),
        (`None, none, maxPrec),
        (`True, tt, maxPrec),
        (`False, ff, maxPrec),
        (numLitKind, num, maxPrec),
        (`«$», num, maxPrec),
        (scientificLitKind, scientific, maxPrec),
        (`«$», scientific, maxPrec),
        (strLitKind, str, maxPrec),
        (`«$», str, maxPrec),
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
        (`«.», attr, 110),
        (`«[», access, 110)
      },
    }
    pFn := prattParserAntiquot expKind "exp" parsingTables
    p (prec : Nat := 0) := precCache expKind pFn ["expression"] expTokens prec

  unsafe def pIdx : Parser :=
    p
  where
    ellipsis := leading_parser "..."
    coord    := leading_parser pExp
    slice    := leading_parser
      Parser.optional pExp >> ":" >> Parser.optional pExp >>
        Parser.optional (":" >> Parser.optional pExp)
    parsingTables := {
      leadingTable := {
        (`«...», ellipsis, maxPrec)
      },
      leadingParsers := [
        (slice, maxPrec),
        (coord, maxPrec)
      ]
    }
    pFn := prattParserAntiquot idxKind "idx" parsingTables
    p := precCache idxKind pFn ["index expression"] idxTokens 0

  end

  /--
  Simpliefied version of `expressions` in `python.gram`.

  Note: While this can technically be written with let-bindings instead of
  where-bindings, the leading node does not work properly with let-bindings,
  which leads to incorrect expansions.
  -/
  unsafe def pExps : Parser :=
    p
  where
    single := leading_parser:maxPrec pExp
    tuple  := leading_parser:maxPrec
      pExp >> "," >> Parser.optional (Parser.sepBy1 pExp "," (allowTrailingSep := true))
    parsingTables := {
      leadingParsers := [
        (single, maxPrec),
        (tuple, maxPrec)
      ]
    }
    pFn := prattParserAntiquot expsKind "exps" parsingTables
    p := precCache expsKind pFn ["expression"] [","] 0

  unsafe def pPat : Parser :=
    p
  where
    id             := Parser.ident
    paren          := leading_parser "(" >> p >> ")"
    tuple          := trailing_parser "," >> Parser.sepBy p "," (allowTrailingSep := true)
    parsingTables  := {
      leadingTable := {
        (`«(», paren, maxPrec),
        (identKind, id, maxPrec),
        (`«$», id, maxPrec)
      },
      trailingTable := {
        (`«,», tuple, maxPrec)
      }
    }
    pFn := prattParserAntiquot patKind "pat" parsingTables
    p := precCache patKind pFn ["binding pattern"] ["(", ")", ","] 0

  -- Simple statement parsers
  def simplStmtTokens : List Token := [
    "=", "+=", "-=", "*=", "@=", "/=", "%=", "**=", "//=",
    "return", "assert", "pass", "break", "continue",
    "import", "from", "as"
  ]

  -- Helper parser for dotted names like "os.path"
  def pDottedName : Parser :=
    withAntiquot
      (mkAntiquot "dottedName" dottedNameKind false true)
      (Parser.sepBy1 Parser.ident "." (allowTrailingSep := false))

  unsafe def pSimplStmt : Parser :=
    p
  where
    ass := leading_parser pPat >> Parser.optional (":" >> pTyp) >> "=" >> pExps
    expStmt := leading_parser pExps
    ret := leading_parser "return" >> Parser.optional pExp
    asrt := leading_parser "assert" >> pExp
    pass := leading_parser "pass"
    brk := leading_parser "break"
    cont := leading_parser "continue"
    imprt := leading_parser "import" >> pDottedName >> Parser.optional ("as" >> Parser.ident)
    imprtFrom := leading_parser "from" >> pDottedName >> "import" >> Parser.ident >> Parser.optional ("as" >> Parser.ident)

    parsingTables := {
      leadingTable := {
        (`return, ret, maxPrec),
        (`assert, asrt, maxPrec),
        (`pass, pass, maxPrec),
        (`break, brk, maxPrec),
        (`continue, cont, maxPrec),
        (`import, imprt, maxPrec),
        (`from, imprtFrom, maxPrec)
      },
      leadingParsers := [
        (ass, maxPrec),
        (expStmt, maxPrec)
      ]
    }
    pFn := prattParserAntiquot simplStmtKind "simplStmt" parsingTables
    p := precCache simplStmtKind pFn ["statement"] simplStmtTokens 0

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

  def eIdent : TSyntax `ident → Ident :=
    Name.toString ∘ TSyntax.getId

  partial def eTyp (stx : TSyntax typKind) : EvalM Typ := do
    let pos ← .getPos stx
    let typ : Typ' ←
      match stx with
      | `(pTyp| $id:ident) => pure <| .var <| eIdent id
      | `(pTyp| None) => pure <| .prim .none
      | `(pTyp| bool) => pure <| .prim .bool
      | `(pTyp| int) => pure <| .prim <| .numeric .int
      | `(pTyp| float) => pure <| .prim <| .numeric .float
      | `(pTyp| str) => pure <| .prim .string
      | `(pTyp| tuple[ $[$ts:typ],* ]) => do
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

  partial def eArgs (pos : Pos) (args : Array (TSyntax argKind)) : EvalM (Array Arg) := do
    let args ← args.mapM (fun arg =>
      match arg with
      | `(pExp.arg| $[$id:ident =]? $e:exp) => do
        pure ⟨id.map eIdent, ← eExp e⟩
      | _ => .throwUnsupportedSyntax pos
    )
    pure args

  partial def eIdx : TSyntax idxKind → EvalM Index
    | `(pIdx| ...) => pure .ellipsis
    | `(pIdx| $e:exp) => do pure <| .coord <| ← eExp e
    | `(pIdx| $[$l:exp]? : $[$u:exp]? $[ : $[$step:exp]? ]?) => do
      let l ← l.mapM eExp
      let u ← u.mapM eExp
      let step ← (step.getD none).mapM eExp
      pure <| .slice l u step
    | stx => do .throwUnsupportedSyntax (← .getPos stx)

  partial def eExp (stx : TSyntax expKind) : EvalM Exp := do
    let pos ← .getPos stx
    match stx with
    | `(pExp| ($e:exp)) => eExp e
    | `(pExp| $id:ident) => pure ⟨pos, .var <| eIdent id⟩
    | `(pExp| None) => pure ⟨pos, .value .none⟩
    | `(pExp| True) => pure ⟨pos, .value <| .bool true⟩
    | `(pExp| False) => pure ⟨pos, .value <| .bool false⟩
    | `(pExp| $n:num) => pure ⟨pos, .value <| .int <| n.getNat⟩
    | `(pExp| $n:scientific) =>
      -- See: `Lean.TSyntax.getScientific`
      match n.getScientific with
      | (0, false, 0) => .throwAt pos "malformed float literal"
      | (n, sign, e) =>
        let f := if sign then n.toFloat * 10 ^ (-e.toFloat) else n.toFloat * 10 ^ e.toFloat
        pure ⟨pos, .value <| .float f⟩
    | `(pExp| $s:str) => pure ⟨pos, .value <| .string <| Python.Parser.getString s⟩
    | `(pExp| $b:exp ** $e:exp) => do pure ⟨pos, .binOp .pow (← eExp b) (← eExp e)⟩
    | `(pExp.neg| -$e:exp) => do pure ⟨pos, .unaryOp .neg (← eExp e)⟩
    | `(pExp| $x:exp * $y:exp) => do pure ⟨pos, .binOp .mul (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp / $y:exp) => do pure ⟨pos, .binOp .div (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp // $y:exp) => do pure ⟨pos, .binOp .floor (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp % $y:exp) => do pure ⟨pos, .binOp .mod (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp + $y:exp) => do pure ⟨pos, .binOp .add (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp - $y:exp) => do pure ⟨pos, .binOp .sub (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp >= $y:exp) => do pure ⟨pos, .binOp .ge (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp > $y:exp) => do pure ⟨pos, .binOp .gt (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp <= $y:exp) => do pure ⟨pos, .binOp .le (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp < $y:exp) => do pure ⟨pos, .binOp .lt (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp != $y:exp) => do pure ⟨pos, .binOp .ne (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp == $y:exp) => do pure ⟨pos, .binOp .eq (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp and $y:exp) => do pure ⟨pos, .binOp .land (← eExp x) (← eExp y)⟩
    | `(pExp| $x:exp or $y:exp) => do pure ⟨pos, .binOp .lor (← eExp x) (← eExp y)⟩
    | `(pExp| $thn:exp if $cond:exp else $els:exp) => do pure ⟨pos, .ifExp (← eExp cond) (← eExp thn) (← eExp els)⟩
    | `(pExp| ($fst:exp, $[$rest:exp],*)) => do
      let fst ← eExp fst
      let rest ← rest.mapM eExp
      pure ⟨pos, .tuple (fst :: rest.toList)⟩
    | `(pExp| $f:exp [ $[$typArgs:typ],* ] ( $[$args:arg],* )) => do
      let f ← eExp f
      let typArgs ← typArgs.mapM eTyp
      let args ← eArgs pos (args.map (⟨·⟩))
      pure ⟨pos, .call f typArgs.toList args.toList⟩
    | `(pExp| $f:exp ( $[$args:arg],* )) => do
      let f ← eExp f
      let args ← eArgs pos (args.map (⟨·⟩))
      pure ⟨pos, .call f [] args.toList⟩
    | `(pExp| $e:exp.$f:ident) => do
      let e ← eExp e
      let f := eIdent f
      pure ⟨pos, .attr e f⟩
    | `(pExp| [$[$es:exp],*]) => do
      let es ← es.mapM eExp
      pure ⟨pos, .list es.toList⟩
    | `(pExp| $e:exp[ $[$idxes:idx],* ]) => do
      let e ← eExp e
      let idxes ← idxes.mapM eIdx
      pure ⟨pos, .access e idxes.toList⟩
    | _ => .throwUnsupportedSyntax pos

  end

  def eExps (stx : TSyntax expsKind) : EvalM Exp := do
    let pos ← .getPos stx
    match stx with
    | `(pExps| $e:exp) =>
      eExp e
    | `(pExps| $e:exp, $[ $[$es:exp],* ]?) =>
      let es ←
        match es with
        | some es => (e :: es.toList).mapM eExp
        | none => pure [← eExp e]
      pure ⟨pos, .tuple es⟩
    | _ => .throwUnsupportedSyntax pos

  partial def ePat : TSyntax patKind → EvalM Pattern
    | `(pPat| ($p:pat)) => ePat p
    | `(pPat| $id:ident) => pure <| .var <| eIdent id
    | `(pPat| $p:pat, $[ $ps:pat ],*) => do
      let ps ← (p :: ps.toList).mapM ePat
      pure <| .tuple ps
    | stx => do .throwUnsupportedSyntax (← .getPos stx)

  def eDottedName : TSyntax dottedNameKind → EvalM QualifiedIdent
    | `(pDottedName| $[$ids:ident].*) => do
      let qualifers := ids.pop.toList.map eIdent
      let name := eIdent ids.back!
      pure (qualifers, name)
    | stx => do .throwUnsupportedSyntax (← .getPos stx)

  def eSimplStmt (stx : TSyntax simplStmtKind) : EvalM Stmt := do
    let pos ← .getPos stx
    match stx with
    | `(pSimplStmt| $p:pat $[: $t:typ]? = $e:exps) =>
      let p ← ePat p
      let t ← t.mapM eTyp
      let e ← eExps e
      pure ⟨pos, .assign p t e⟩
    | `(pSimplStmt| return $[$e:exp]?) =>
      let e ← match e with
        | some e => eExp e
        | none => pure ⟨pos, .value .none⟩
      pure ⟨pos, .ret e⟩
    | `(pSimplStmt| assert $e:exp) =>
      let e ← eExp e
      pure ⟨pos, .assert e⟩
    | `(pSimplStmt| pass) =>
      pure ⟨pos, .pass⟩
    | `(pSimplStmt| break) =>
      pure ⟨pos, .breakLoop⟩
    | `(pSimplStmt| continue) =>
      pure ⟨pos, .continueLoop⟩
    | `(pSimplStmt| $e:exps) =>
      let e ← eExps e
      pure ⟨pos, .exp e⟩
    | `(pSimplStmt| import $imp:dottedName $[as $alias_:ident]?) =>
      let imp ← eDottedName imp
      let alias_ := alias_.map eIdent
      pure ⟨pos, .imprt imp alias_⟩
    | `(pSimplStmt| from $frm:dottedName import $imp:ident $[as $alias_:ident]?) =>
      let frm ← eDottedName frm
      let imp := eIdent imp
      let alias_ := alias_.map eIdent
      pure ⟨pos, .imprtFrom frm imp alias_⟩
    | _ => .throwUnsupportedSyntax pos

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
def pyTokens : TokenTable :=
  TokenTable.empty ++ Parse.typTokens ++ Parse.expTokens ++ Parse.idxTokens ++ Parse.simplStmtTokens

def runPyParser (source fileName : String) (fileMap : FileMap) : IO (Except String Syntax) := unsafe do
  let p := Parse.pSimplStmt
  let s ← runParser source fileName (p >> Parser.eoi) pyTokens
  if s.hasError then
    let { line, column } := fileMap.toPosition s.pos
    return .error s!"{fileName} {line}:{column}: {s.errorMsg.get!.toString}"
  else
    return .ok s.stxStack.back

def evalPy (source fileName : String) : IO (Except String Stmt) := do
  let fileMap := source.toFileMap
  let stx ←← runPyParser source fileName fileMap
  match ((Eval.eSimplStmt ⟨stx⟩).run { fileMap }).run {} with
  | .ok (res, _) _ => return .ok res
  | .error err _ => return .error err.msg

def str := "(a,b),c : tuple[tuple[int, int], int] = ((0,0), 1)"
#eval return (←←evalPy str "<input>")

def testExp := "foo[1]"
#eval return toJson (←←evalPy testExp "<input>")

-- Test additional statements
def testReturn := "return 42"
#eval return (←←evalPy testReturn "<input>")

def testAssert := "assert x > 0"
#eval return (←←evalPy testAssert "<input>")

def testPass := "pass"
#eval return (←←evalPy testPass "<input>")

def testBreak := "break"
#eval return (←←evalPy testBreak "<input>")

def testContinue := "continue"
#eval return (←←evalPy testContinue "<input>")

-- Test import statements
def testImport := "import math"
#eval return (←←evalPy testImport "<input>")

def testImportAs := "import numpy as np"
#eval return (←←evalPy testImportAs "<input>")

def testImportDotted := "import os.path"
#eval return (←←evalPy testImportDotted "<input>")

def testImportDottedAs := "import os.path as ospath"
#eval return (←←evalPy testImportDottedAs "<input>")

def testFromImport := "from math import sin"
#eval return (←←evalPy testFromImport "<input>")

def testFromImportAs := "from math import sin as sine"
#eval return (←←evalPy testFromImportAs "<input>")

def testFromImportDotted := "from os.path import join"
#eval return (←←evalPy testFromImportDotted "<input>")
