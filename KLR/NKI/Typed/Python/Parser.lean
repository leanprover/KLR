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

inductive Assoc | l | r | n

def opTable {α} [Inhabited α] (l : List (Nat × Assoc × String × α)) : Parser α :=
  let ps : List (Parser α) := l.map (fun (prec, assoc, t, op) =>
    let (l, r) :=
      match assoc with
      | .l => (prec, prec + 1)
      | .r => (prec, prec)
      | .n => (prec - 1, prec)
    .trailingPrec l r (.action (tk t) fun () => op)
  )
  match ps with
  | [] => .action .empty fun () => Inhabited.default
  | hd :: tl => tl.foldl .choice hd

def binOp : Parser BinOp :=
  opTable [
    (95, .r, "**", .pow),
    (90, .l, "*", .mul),
    (90, .l, "@", .matmul),
    (90, .l, "/", .div),
    (90, .l, "//", .floor),
    (90, .l, "%", .mod),
    (85, .l, "+", .add),
    (85, .l, "-", .sub),
    (80, .l, "<<", .lshift),
    (80, .l, ">>", .rshift),
    (75, .l, "&", .bitwiseAnd),
    (70, .l, "&", .bitwiseXor),
    (65, .l, "|", .bitwiseOr),
    (60, .n, ">=", .ge),
    (60, .n, ">", .gt),
    (60, .n, "<=", .le),
    (60, .n, "<", .lt),
    (60, .n, "!=", .ne),
    (60, .n, "==", .eq),
    (50, .l, "and", .land),
    (45, .l, "or", .lor),
  ]

def unaryOp : Parser UnaryOp :=
  opTable [
    (100, .r, "-", .neg),
    (100, .r, "+", .pos),
    (100, .r, "~", .bitwiseNot),
    (55, .r, "not", .not),
  ]

def unary : Parser Exp :=
  (mkPos fileMap (
    .action (unaryOp >> expression)
    fun (op, e) => .unaryOp op e
  ) fun e pos => ⟨pos, e⟩)
  <|> primary fileMap

def term : Parser Exp :=
  .action (
    (unary fileMap >> (PExp.star (binOp >> expression)))
  )
  fun (hd, tl) =>
    tl.foldl (fun x (op, y) =>
      ⟨x.pos + y.pos, .binOp op x y⟩
    ) hd

def exp : Parser Exp :=
  (mkPos fileMap (
    .action (
      term fileMap >> "if" >> term fileMap >> "else" >> expression
    ) fun (thn, (), cond, (), els) => .ifExp cond thn els
  ) fun e pos => ⟨pos, e⟩)
  <|> term fileMap

def file : Parser (List Stmt) :=
  .action (.optional (.prod NT.statements)) (·.getD [])

def augassign : Parser BinOp :=
  p "+=" .add
  <|> p "-=" .sub
  <|> p "*=" .mul
  <|> p "@=" .matmul
  <|> p "/=" .div
  <|> p "%=" .mod
  <|> p "&=" .bitwiseAnd
  <|> p "|=" .bitwiseOr
  <|> p "^=" .bitwiseXor
  <|> p "<<=" .lshift
  <|> p ">>=" .rshift
  <|> p "**=" .pow
  <|> p "//=" .floor
where
  p s op :=
    .action (tk s) fun () => op

def assignment : Parser Stmt' :=
  (.action (expressions fileMap >> PExp.optional (":" >> expression) >> "=" >> expressions fileMap)
  fun (lhs, anno, (), rhs) => .assign lhs (anno.map Prod.snd) rhs)
  <|> .action (expression >> augassign >> expression)
      fun (lhs, op, rhs) => .assign lhs none ⟨lhs.pos + rhs.pos, .binOp op lhs rhs⟩

def returnStmt : Parser Stmt' :=
  mkPos fileMap (
    .action ("return" >> PExp.optional expression) Prod.snd
  ) fun e pos => .ret (e.getD ⟨pos, .value .none⟩)

def dottedName : Parser QualifiedIdent :=
  .action (name >> PExp.star ("." >> name))
  fun (hd, tl) =>
    let tl := tl.map Prod.snd
    let name := tl.getLastD hd
    let quals :=
      match tl with
      | [] => []
      | tl => hd :: (tl.take (tl.length - 1))
    (quals, name)

def importStmt : Parser Stmt' :=
  (.action (
    "from" >> dottedName >> "import" >> name >> PExp.optional ("as" >> name)
  ) fun ((), mod, (), imp, as) => .imprtFrom mod imp (as.map Prod.snd))
  <|> (.action (
    "import" >> dottedName >> PExp.optional ("as" >> name)
  ) fun ((), mod, as) => .imprt mod (as.map Prod.snd))

def simpleStmt : Parser Stmt :=
  mkPos fileMap (
    assignment fileMap
    <|> (.action expression Stmt'.exp)
    <|> returnStmt fileMap
    <|> importStmt
    <|> (.action "pass" fun () => Stmt'.pass)
    <|> (.action ("assert" >> expression) (.assert ·.snd))
    <|> (.action "break" fun () => Stmt'.breakLoop)
    <|> (.action "continue" fun () => Stmt'.continueLoop)
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

def decorators : Parser (List Exp) :=
  .action (.star <| "@" >> expression >> newline)
  fun l => l.map (Prod.fst ∘ .snd)

def param : Parser Param :=
  .action (
    name >> PExp.optional (":" >> expression) >> PExp.optional ("=" >> expression)
  ) fun (name, typ, dflt) =>
    let typ := typ.map Prod.snd
    let dflt := dflt.map Prod.snd
    { name, typ, dflt }

def functionDef : Parser Stmt' :=
  .action (
    decorators >>
    "def" >> name >> PExp.optional (bracketList name true) >> parenList param
    >> PExp.optional ("->" >> expression) >> ":" >> block fileMap
  ) fun (decorators, (), name, typs, params, returns, (), body) =>
    let f : FuncDef := {
      name,
      typParams := typs.getD [],
      params,
      returns := returns.map Prod.snd,
      body,
      decorators
    }
    .funcDef f

def ifStmt : Parser Stmt' :=
  .action (
    "if" >> expression >> ":" >> block fileMap
    >> PExp.star ("elif" >> expression >> ":" >> block fileMap)
    >> PExp.optional ("else" >> ":" >> block fileMap)
  ) fun ((), cond, (), thn, elifs, els) =>
    let elifs := elifs.map fun ((), cond, (), body) => (cond, body)
    let els := els.map (Prod.snd ∘ .snd)
    .ifStm cond thn elifs els

def whileStmt : Parser Stmt' :=
  .action (
    "while" >> expression >> ":" >> block fileMap
  ) fun ((), cond, (), body) => .whileLoop cond body

def compountStmt : Parser Stmt :=
  mkPos fileMap (
    functionDef fileMap
    <|> ifStmt fileMap
    <|> forStmt fileMap
    <|> whileStmt fileMap
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

def run (input : String) (fileName : String) (fileMap : FileMap := input.toFileMap) : Except String Prog := do
  let tks ← Tokenizer.run input fileName fileMap
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

def input := "
def foo():
  a = (1 * 2) * 3
  pass
"
#eval run input "<input>"
#eval (run input "<input>").map Lean.toJson
