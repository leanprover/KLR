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

/-
https://docs.python.org/3/reference/grammar.html
-/

import KLR.Core
import KLR.NKI.Typed.Python.Basic
import KLR.NKI.Typed.Python.PrettyPrint
import KLR.NKI.Typed.Python.PegParser
import KLR.NKI.Typed.Python.Tokenizer
import KLR.NKI.Typed.Python.Util

namespace KLR.NKI.Typed.Python

namespace Tokenizer

@[simp]
def TokenKind.kindEq : TokenKind → TokenKind → Bool
  | .int _, .int _
  | .float _, .float _
  | .string _, .string _
  | .ident _, .ident _ => true
  | t1, t2 => t1 == t2

@[simp]
abbrev TokenKind.denote : TokenKind → Type
  | .int _ => Int
  | .float _ => Float
  | .string _ => String
  | .ident _ => Ident
  | _ => Unit

def TokenKind.data (t : TokenKind) : t.denote :=
  match t with
  | .int i => i
  | .float f => f
  | .string s => s
  | .ident id => id
  | .tokenLit _ | .newline | .indent | .dedent => ()

theorem TokenKind.kindEq_sound : ∀ (t1 t2 : TokenKind), t1.kindEq t2 → t1.denote = t2.denote := by
  intro t1 t2 heq
  simp_all [kindEq, BEq.beq, denote]
  split at heq
  <;> aesop

def Token.kindEq (t1 t2 : Token) : Bool :=
  t1.kind.kindEq t2.kind

abbrev Token.denote (t : Token) : Type :=
  t.kind.denote

def Token.data (t : Token) : t.denote :=
  t.kind.data

theorem Token.kindEq_sound (t1 t2 : Token) (h : t1.kindEq t2) : t1.denote = t2.denote :=
  TokenKind.kindEq_sound t1.kind t2.kind h

end Tokenizer

namespace Parser

open Lean (FileMap)
open KLR.Core (Pos)
open Tokenizer (Token)
open PegParser (PExp)

instance : Add Pos where
  add x y := {
    line := x.line,
    column := x.column,
    lineEnd := y.lineEnd.getD y.line,
    columnEnd := y.columnEnd.getD y.column
  }

inductive NT
  | file
  | statements
  | expression
  | pattern
  -- | primary

abbrev NT.denote : NT → Type
  | .file => List Stmt
  | .statements => List Stmt
  | .expression => Exp
  | .pattern => Pattern
  -- | .primary => Exp

abbrev Parser := PExp Token NT Token.denote NT.denote

section
variable (fileMap : FileMap)

def mkPos {α β} (p : Parser α) (f : α → Pos → β) : Parser β :=
  .withPos p fun a sp ep =>
    let { line, column } := fileMap.toPosition sp
    let { line := lineEnd, column := columnEnd } := fileMap.toPosition ep
    let pos : Pos := {line, column, lineEnd, columnEnd}
    f a pos

def newline : Parser Unit :=
  .token (⟨.newline, {}, {}⟩ : Token)

def indent : Parser Unit :=
  .token (⟨.indent, {}, {}⟩ : Token)

def dedent : Parser Unit :=
  .token (⟨.dedent, {}, {}⟩ : Token)

def tk (s : String) : Parser Unit :=
  .token (⟨.tokenLit s, {}, {}⟩ : Token)

instance : Coe String (Parser Unit) := ⟨tk⟩

instance {α} : HAndThen String (Parser α) (Parser (Unit × α)) where
  hAndThen a b := tk a >> (b ())

instance {α} : HAndThen (Parser α) String (Parser (α × Unit)) where
  hAndThen a b := a >> tk (b ())

instance : HAndThen String String (Parser (Unit × Unit)) where
  hAndThen a b := tk a >> tk (b ())

def parenList {α} (p : Parser α) (notEmpty : Bool := false) : Parser (List α) :=
  let sepBy := if notEmpty then PExp.sepBy1 else PExp.sepBy
  .action ("(" >> sepBy p (tk ",") >> ")") fun ((), res, ()) => res

def bracketList {α} (p : Parser α) (notEmpty : Bool := false) : Parser (List α) :=
  let sepBy := if notEmpty then PExp.sepBy1 else PExp.sepBy
  .action ("[" >> sepBy p (tk ",") >> "]") fun ((), res, ()) => res

/--
NOTE: This is only called by other parsers to handle setting the precedence.
The parser that is acutally passed to `Production` must be `exp`, since that one
actually register the rules.
-/
@[inline] def expression (p : Option Nat := none) : Parser Exp :=
  match p with
  | some p => .leadingPrec p <| .prod NT.expression
  | none => .prod NT.expression

-- @[inline] def primary (p : Option Nat := none) : Parser Exp :=
--   match p with
--   | some p => .leadingPrec p <| .prod NT.primary
--   | none => .prod NT.primary

def expressions : Parser Exp :=
  (mkPos fileMap (
    .action (
      expression >> "," >> PExp.sepBy expression (tk ",")
    ) fun (hd, (), tl) => .tuple (hd :: tl)
  ) fun e pos => ⟨pos, e⟩)
  <|> expression

def numLit : Parser Exp' :=
  (.action (.token ⟨.int 0, {}, {}⟩) fun i => .value (.int i))
  <|> (.action (.token ⟨.float 0, {}, {}⟩) fun f => .value (.float f))

def strLit : Parser Exp' :=
  .action (.token ⟨.string "", {}, {}⟩) fun s => .value (.string s)

def name : Parser Ident :=
  .token (⟨.ident "", {}, {}⟩ : Token)

def atom : Parser Exp :=
  (mkPos fileMap (
    (.action name fun id => .var id)
    <|> numLit <|> strLit
    <|> (.action (bracketList expression) Exp'.list)
    <|> (.action "..." fun () => .value .ellipsis)
  ) fun e pos => ⟨pos, e⟩)
  <|> (.action ("(" >> expressions fileMap >> ")") (Prod.fst ∘ Prod.snd))

inductive PrimaryRhs
  | attr (f : Ident)
  | call (typs : List Exp) (args : List Arg)
  | access (indices : List Index)

def index : Parser Index :=
  (.action (
    PExp.optional expression >> ":" >> PExp.optional expression
    >> PExp.optional (":" >> PExp.optional expression)
  ) fun (l, (), u, step) => .slice l u ((step.map Prod.snd).getD none))
  <|> .action expression Index.coord

def arg : Parser Arg :=
  (.action (name >> "=" >> expression) fun (keyword, (), val) => {keyword, val})
  <|> (.action expression fun val => {val})

def primaryRhs : Parser (PrimaryRhs × Pos) :=
  mkPos fileMap (
    .trailingPrec 120 121 (.action ("." >> name) fun ((), f) => .attr f)
    <|> .trailingPrec 120 121
        (.action (bracketList expression true >> parenList arg)
          fun (typs, args) => .call typs args)
    <|> .trailingPrec 115 116
        (.action (bracketList index true)
          fun (indices) => .access indices)
    <|> .trailingPrec 120 121
        (.action (parenList arg)
          fun (args) => .call [] args))
  fun rhs pos => (rhs, pos)

def primary : Parser Exp :=
  .action (
    atom fileMap >> (PExp.star <| primaryRhs fileMap)
  ) fun (e, rhs) =>
      rhs.foldl (fun e (rhs, pos) =>
        let pos := e.pos + pos
        match rhs with
        | .attr f => ⟨pos, .attr e f⟩
        | .call typs args => ⟨pos, .call e typs args⟩
        | .access indices => ⟨pos, .access e indices⟩
      ) e

def binOp : Parser BinOp :=
      .trailingPrec 90 91 (.action "*" fun () => .mul)
  <|> .trailingPrec 85 86 (.action "+" fun () => .add)

def exp : Parser Exp :=
  .action (
    (primary fileMap >> (PExp.star (binOp >> expression)))
  )
  fun (hd, tl) =>
    tl.foldl (fun x (op, y) =>
      ⟨x.pos + y.pos, .binOp op x y⟩
    ) hd

def file : Parser (List Stmt) :=
  .action (.optional (.prod NT.statements)) (·.getD [])

def simpleStmt : Parser Stmt :=
  mkPos fileMap (
    (.action (.prod .expression) Stmt'.exp)
    <|> (.action "pass" fun () => Stmt'.pass)
    <|> (.action "break" fun () => Stmt'.breakLoop)
  ) fun s pos => ⟨pos, s⟩

def simpleStmts : Parser (List Stmt) :=
  .action (PExp.sepBy1 (simpleStmt fileMap) (tk ";") >> newline) Prod.fst

def block : Parser (List Stmt) :=
  (.action (newline >> indent >> (.prod NT.statements : Parser (List Stmt)) >> dedent)
    fun ((), (), s, ()) => s)
  <|> simpleStmts fileMap

def patternAtom : Parser Pattern :=
  (.action name fun s => .var s)
  <|> (.action ("(" >> (.prod NT.pattern : Parser Pattern) >> ")")
        (Prod.fst ∘ .snd))

def pattern : Parser Pattern :=
  (.action (
    patternAtom >> "," >> PExp.sepBy patternAtom (tk ",")
  ) fun (hd, (), tl) => .tuple (hd :: tl))
  <|> patternAtom

def forStmt : Parser Stmt' :=
  .action (
    "for" >> pattern >> "in" >> expressions fileMap >> ":" >> block fileMap
  ) fun ((), p, (), e, (), b) => .forLoop p e b

def compountStmt : Parser Stmt :=
  mkPos fileMap (
    forStmt fileMap
  ) fun s pos => ⟨pos, s⟩

def statements : Parser (List Stmt) :=
  .action (
    .many1 (
      (.action (compountStmt fileMap) List.singleton)
      <|> simpleStmts fileMap
    )
  ) List.flatten

end

def prods (fileMap : FileMap) : PegParser.Production Token NT Token.denote NT.denote := fun n =>
  match n with
  | .file => file
  | .statements => statements fileMap
  | .expression => exp fileMap
  | .pattern => pattern
  -- | .primary => prim fileMap

def run (input : String) (fileName : String) (fileMap : FileMap := input.toFileMap) : Except String Prog := do
  let tks ← Tokenizer.run input fileName fileMap
  -- dbg_trace Tokenizer.Test.tokensToString tks
  let c : PegParser.Context Token NT Token.denote NT.denote := {
    input := tks,
    tkEq := Token.kindEq,
    tkEq_sound := Token.kindEq_sound,
    tkData := Token.data,
    tkStartPos := Token.pos,
    tkEndPos := Token.endPos,
    tkToString tk :=
      match tk.kind with
      | .int _ | .float _ => "numeric literal"
      | .ident _ => "identifier"
      | .string _ => "string literal"
      | .tokenLit s => s
      | .newline => "newline"
      | .dedent => "dedent"
      | .indent => "indent",
    errFormat msg startPos endPos := formatErrorPure fileName fileMap "Syntax Error" msg startPos endPos
  }
  let p := prods fileMap
  let stmts ← PExp.run p .file c
  .ok { file := fileName, stmts }

def input := "a[1]()\n"
#eval run input "<input>"
#eval (run input "<input>").map Lean.toJson
