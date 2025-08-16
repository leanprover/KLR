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

import KLR.Py.Basic
import KLR.Py.Tokenizer
import KLR.Py.Pretty
import Std.Data.HashMap.Basic

namespace KLR.Py.Parser

open Tokenizer (Token)

def Token.hash (t : Token) : UInt64 :=
  let s :=
    match t.kind with
    | .tokenLit s => s
    | .ident _    => "ident"
    | .int _      => "int"
    | .float _    => "float"
    | .string _   => "string"
    | .newline    => "newline"
    | .indent     => "indent"
    | .dedent     => "dedent"
  s.hash

def Token.kindEq (t1 t2 : Token) : Bool :=
  match t1.kind, t2.kind with
  | .tokenLit x, .tokenLit y => x == y
  | .ident _, .ident _
  | .int _, .int _
  | .float _, .float _
  | .string _, .string _
  | .newline, .newline
  | .indent, .indent
  | .dedent, .dedent => true
  | _, _ => false

def TokenMap (α : Type) := @Std.HashMap Token α ⟨Token.kindEq⟩ ⟨Token.hash⟩

def TokenMap.emptyWithCapacity {α} (c : Nat) : TokenMap α :=
  @Std.HashMap.emptyWithCapacity Token α ⟨Token.kindEq⟩ ⟨Token.hash⟩ c

instance {α} : Singleton (Token × α) (TokenMap α) where
  singleton a := (TokenMap.emptyWithCapacity 8).insert a.1 a.2

instance {α} : Insert (Token × α) (TokenMap α) where
  insert a m := m.insert a.1 a.2

structure Context where
  input    : Array Token
  fileInfo : FileInfo

structure State where
  pos : Nat         := 0
  err : List String := []

abbrev ParserM := ReaderT Context <| OptionT <| StateM State

/--
Propagate error messages, but save the original position on failure
-/
def ParserM.bind {α β} (a : ParserM α) (f : α → ParserM β) : ParserM β := fun c s =>
  let (a?, s') := a c s
  match a? with
  | some a =>
    let (b?, s') := f a c s'
    match b? with
    | some b => (b, s')
    | none   => (none, {s with err := s'.err})
  | none => (none, {s with err := s'.err})

instance : Bind ParserM := ⟨ParserM.bind⟩

def fail {α} : ParserM α :=
  fun _ s => (none, s)

def Context.formatError (c : Context) (msg : String) (pos : Pos) : String :=
  c.fileInfo.formatError "SyntaxError" msg pos

def pushErr (msg : String) (pos : Pos) : ParserM Unit := do
  let msg := (← read).formatError msg pos
  modifyGet fun s => ((), {s with err := msg :: s.err})

def notSupported := [
  "await",
  "except",
  "raise",
  "class",
  "finally",
  "is",
  "lambda",
  "try",
  "as",
  "nonlocal",
  "global",
  "async",
  "yield",
]

def getInput : ParserM (Array Token) :=
  return (← read).input

def getPos : ParserM Nat :=
  return (← get).pos

def peekAt (i : Nat) : ParserM (Option Token) :=
  return (← read).input[i]?

def peek : ParserM (Option Token) := do
  peekAt (← getPos)

def consume : ParserM Unit :=
  modifyGet fun s => ((), {s with pos := s.pos + 1})

def withPos {α β} (f : Pos → α → β) (p : ParserM α) : ParserM β := do
  let some curr ← peek | fail
  let i ← getPos
  let a ← p
  let j ← getPos
  if i ≥ j then pushErr "internal error: failed to get position infomataion" curr.pos; fail else
  let some last ← peekAt (j - 1) | pushErr "internal error: failed to get position information" curr.pos; fail
  return f ⟨curr.pos.pos, last.pos.stopPos⟩ a

def withErr {α} (msg : String) (pos : Option Pos) (p : ParserM α) : ParserM α := fun c s =>
  let (a?, s) := p c s
  match a? with
  | some a => (a, s)
  | none =>
    let msg :=
      match pos with
      | some pos => c.formatError msg pos
      | none =>
        match c.input[s.pos]? with
        | some ⟨_, pos⟩ => c.formatError msg pos
        | none => msg
    (none, {s with err := msg :: s.err})

/--
NOTE: For performance, `b` is not called if `a` fails.
So if `b` contained error reporting with `withErr`, it will get lost.
-/
instance {α β} : HAndThen (ParserM α) (ParserM β) (ParserM (α × β)) where
  hAndThen a b := do
    let a ← a
    let b ← b ()
    pure (a, b)

def not {α} (p : ParserM α) (msg : String) : ParserM Unit := fun c s =>
  match c.input[s.pos]? with
  | none => (some (), s)
  | some curr =>
    let (a?, _) := p c s
    match a? with
    | some _ =>
      let err := c.formatError msg curr.pos
      (none, {s with err := err :: s.err})
    | none => (some (), s)

def many {α} (p : ParserM α) : ParserM (Array α) := do
  let input ← getInput
  let rec go (arr : Array α) (i : Nat) : ParserM (Array α × Nat) := fun c s =>
    let (a?, s) := p c {s with pos := i}
    match a? with
    | some a =>
      if s.pos ≤ i then ((arr, i), {s with pos := i}) else
      if s.pos ≥ input.size then ((arr, s.pos), s) else
      go (arr.push a) s.pos c s
    | none => ((arr, i), s)
  termination_by input.size - i
  Prod.fst <$> go #[] (← getPos)

def optional {α} (p : ParserM α) : ParserM (Option α) := fun c s =>
  let (a?, s) := p c s
  (some a?, s)

def sepBy1 {α β} (p : ParserM α) (sep : ParserM β) (allowTrailing : Bool := true) : ParserM (Array α) := do
  let fst ← p
  let rst ← many (sep >> p)
  if allowTrailing then _ ← optional sep
  let rst := Prod.snd <$> rst
  return #[fst] ++ rst

def sepBy {α β} (p : ParserM α) (sep : ParserM β) (allowTrailing : Bool := true) : ParserM (Array α) :=
  (fun as => as.getD #[]) <$> optional (sepBy1 p sep allowTrailing)

def mkTokenMap {α} (l : List (String × α)) : TokenMap α :=
  let l := l.map fun (t, a) => (⟨.tokenLit t, {}⟩, a)
  l.foldl
    (fun s (t, a) => s.insert t a)
    (.emptyWithCapacity l.length)

def token (s : String) : ParserM Unit := do
  let some ⟨.tokenLit curr, _⟩ ← peek | fail
  if curr == s then consume else fail

def name : ParserM Ident := do
  let some ⟨.ident id, _⟩ ← peek | fail
  consume; return id

def numLit : ParserM Exp' := do
  let some ⟨t, _⟩ ← peek | fail
  let some e :=
    (match t with
      | .int n   => Exp'.value <| .int n
      | .float n => Exp'.value <| .float n
      | _        => none) | fail
  consume; return e

def strLit : ParserM Exp' := do
  let some ⟨.string s, _⟩ ← peek | fail
  consume; return .value <| .string s

inductive Assoc
  | l | r | n
deriving BEq

instance : ToString Assoc where
  toString | .l => "l" | .r => "r" | .n => "n"

def Assoc.prec (n : Nat) : Assoc → Nat
  | .l => n | .r => n - 1 | .n => n

-- def Assoc.satPrec (prec : Nat) (precLimit : Nat) : Assoc → Bool
--   | .l | .r => prec > precLimit
-- | .n      => prec > precLimit + 1

mutual

partial def tuple : ParserM Exp := do
  let some ⟨.tokenLit "(", pos⟩ ← peek | fail
  consume
  let some hd ← optional exp | do {
    let some ⟨.tokenLit ")", stopPos⟩ ← peek | fail
    consume
    return ⟨⟨pos.pos, stopPos.stopPos⟩, .tuple []⟩
  }
  let some () ← optional (token ",") | { _ ← token ")"; return hd }
  let tl ← sepBy exp (token ",")
  let some ⟨.tokenLit ")", stopPos⟩ ← peek | fail
  consume
  return ⟨⟨pos.pos, stopPos.stopPos⟩, .tuple (hd :: tl.toList)⟩

partial def list : ParserM Exp := do
  let some ⟨.tokenLit "[", pos⟩ ← peek | fail
  consume
  let es ← sepBy exp (token ",")
  let some ⟨.tokenLit "]", stopPos⟩ ← peek | fail
  consume
  return ⟨⟨pos.pos, stopPos.stopPos⟩, .list es.toList⟩

partial def atom : ParserM Exp := do
  -- Don't know if the compiler is smart enough to cache this
  let atomMap : TokenMap (ParserM Exp) := {
    (⟨.ident    ""     , {}⟩, withPos .mk <| Exp'.var <$> name),
    (⟨.int      0      , {}⟩, withPos .mk <| numLit),
    (⟨.float    0      , {}⟩, withPos .mk <| numLit),
    (⟨.tokenLit "True" , {}⟩, withPos .mk <| (fun () => .value (.bool true)) <$> consume),
    (⟨.tokenLit "False", {}⟩, withPos .mk <| (fun () => .value (.bool false)) <$> consume),
    (⟨.string   ""     , {}⟩, withPos .mk <| strLit),
    (⟨.tokenLit "("    , {}⟩,                tuple),
    (⟨.tokenLit "["    , {}⟩,                list)
  }

  let some curr ← peek | fail
  let some p := atomMap.get? curr | fail
  p

partial def unaryOpMap : TokenMap (Nat × UnaryOp) :=
  mkTokenMap [
    ("-", (100, .neg)),
    ("+", (100, .pos)),
    ("~", (100, .bitwiseNot)),
    ("not", (55, .not)),
  ]

partial def binOpMap : TokenMap (Nat × Assoc × BinOp) :=
  mkTokenMap [
    ("**", (95, .r, .pow)),
    ("*", (90, .l, .mul)),
    ("+", (85, .l, .add)),
    (">=", (60, .n, .ge)),
  ]

partial def exp (precLimit : Nat := 0) : ParserM Exp := do
  let some start ← peek | fail
  dbg_trace "exp called: tk={start.kind} precLimit={precLimit}"
  let fst : Exp ←
    match unaryOpMap.get? start with
    | some (prec, op) =>
      if prec + 1 ≤ precLimit then
        pushErr "precedence level is low, consider parentheses" start.pos
        fail
      else
        consume
        let lhs ← exp prec
        pure ⟨⟨start.pos.pos, lhs.pos.stopPos⟩, .unaryOp op lhs⟩
    | none => atom

  let mut lhs := fst
  let mut curr ← peek
  let mut precLimit := precLimit

  while h : curr.isSome do
    let tk := curr.get h
    match binOpMap.get? tk with
    | some (prec, assoc, op) =>
      dbg_trace "op matched: op=({op.reprPrec.1}) assoc={assoc} prec={prec} precLimit={precLimit}"
      if prec ≤ precLimit then
        if assoc == .n then
          pushErr "chaining of comparison operators is not allowed" tk.pos
        else
          pushErr "precedence level is low, consider parentheses" tk.pos
        break
      else
        consume
        let rhs ← exp (assoc.prec prec)
        dbg_trace "rhs"
        lhs := ⟨⟨start.pos.pos, rhs.pos.stopPos⟩, .binOp op lhs rhs⟩
        if assoc == .n then precLimit := prec + 1
    | none =>
      break
    curr ← peek

  return lhs

end

def dottedName : ParserM QualifiedIdent := do
  not (token ".") "implcit current directory not supported"
  let ids ← sepBy1 name (token ".") false
  not (token ".") "did you accidentally left an extra '.' here?"
  return (ids.pop.toList, ids.back!)

def asName : ParserM (Option Ident) := do
  let as ← optional (token "as" >> name)
  not (token "as") "missing qualifier after 'as'"
  return Prod.snd <$> as

/-- Assumes the `import` keyword is already matched -/
def imprt : ParserM Stmt' := do
  consume
  let mod ← dottedName
  not (token "from") "did you meant to do 'from ... import ...' ?"
  let as ← asName
  return .imprt mod as

/-- Assumes the `from` keyword is already matched -/
def fromImprt : ParserM Stmt' := do
  consume
  let mod ← dottedName
  _ ← token "import"
  let imp ← name
  not (token ".") "cannot qualify imports after from"
  let as ← asName
  return .imprtFrom mod imp as

def stmt : ParserM Stmt := withPos .mk do
  let some curr ← peek | fail

  match curr.kind with
  | .tokenLit "import" =>
    withErr "unfinished import statement" curr.pos imprt
  | .tokenLit "from" =>
    withErr "unfinished import statement" curr.pos fromImprt
  | _ =>
    withErr "failed to parse expression" curr.pos (.exp <$> exp)
  -- | .tokenLit "def" =>
  --   sorry
  -- | .tokenLit t =>
  --   if notSupported.contains t then
  --     pushErr s!"'{t}' is not supported" curr.pos
  --     fail
  --   else
  --     sorry
  -- | _ => sorry

def run (input : String) (fileName : String) (fileMap : Lean.FileMap := input.toFileMap) : Except String Stmt := do
  let tks ← Tokenizer.run input fileName fileMap
  let c : Context := {
    input := tks,
    fileInfo := {
      content := input,
      fileName,
      fileMap
    }
  }
  let s : State := {}
  let (stmt?, s) := stmt c s
  match stmt? with
  | some stmt =>
    if h : s.pos < tks.size then
      .error <| s.err.getLast?.getD (c.formatError "invalid syntax" tks[s.pos].pos)
    else
      .ok stmt
  | none =>
    .error <| s.err.getLast?.getD "invalid syntax"

namespace Debug

mutual

def Exp.printTree (e : Exp) : Std.Format :=
  match e with
  | { exp, .. } => Exp'.printTree exp

def Exp'.printTree (e : Exp') : Std.Format :=
  match e with
  | .binOp op x y =>
    let (op, _) := op.reprPrec
    let x := cont ++ nest (Exp.printTree x)
    let y := last ++ nest (Exp.printTree y)
    join [s!"({op})", x, y]
  | .unaryOp op x =>
    let (op, _) := op.reprPrec
    let x := last ++ nest (Exp.printTree x)
    join [s!"({op})", x]
  | .ifExp cond thn els =>
    let cond := cont ++ nest (Exp.printTree cond)
    let thn := cont ++ nest (Exp.printTree thn)
    let els := last ++ nest (Exp.printTree els)
    join ["(ite)", cond, thn, els]
  | _ => e.reprPrec 0
where
  nest x := Std.Format.nest 5 x
  join (l : List Std.Format) := Std.Format.joinSep l "\n"
  cont := " |---"
  last := " '---"

end

def Stmt.printExpTree (s : Stmt) : Std.Format :=
  match s.stmt with
  | .exp e => Exp.printTree e
  | _ => "not an expression"

/--
Print expression trees, used to debug associativity
-/
def Prog.printExpTree (p : Prog) : Std.Format :=
  let es := p.stmts.map Stmt.printExpTree
  Std.Format.joinSep es "\n"

def input := "1 + 1 * - (not 3)"
-- def input := "(1 + 2) * 3"
-- #eval run input "<input>"
#eval (run input "<input>").map Stmt.printExpTree

end Debug
