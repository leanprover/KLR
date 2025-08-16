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

namespace KLR.Py.Parser

open Tokenizer (Token)

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

def token (s : String) : ParserM Unit := do
  let some ⟨.tokenLit curr, _⟩ ← peek | fail
  if curr == s then consume else fail

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

def name : ParserM Ident := do
  let some ⟨.ident id, _⟩ ← peek | fail
  consume; return id

def dottedName : ParserM QualifiedIdent := do
  not (token ".") "implcit current directory not supported"
  let ids ← sepBy1 name (token ".") false
  not (token ".") "did you accidentally left an extra '.' here?"
  return (ids.pop.toList, ids.back!)

def asName : ParserM (Option Ident) := do
  let as ← optional (token "as" >> name)
  not (token "as") "missing qualifier after 'as'"
  return Prod.snd <$> as

def imprt : ParserM Stmt' := do
  consume
  let mod ← dottedName
  not (token "from") "did you meant to do 'from ... import ...' ?"
  let as ← asName
  return .imprt mod as

def fromImprt : ParserM Stmt' := do
  consume
  let mod ← dottedName
  _ ← token "import"
  let imp ← name
  not (token ".") "cannot qualify imports after from"
  let as ← asName
  return .imprtFrom mod imp as

def stmt : ParserM Stmt := withPos Stmt.mk do
  let some curr ← peek | fail

  match curr.kind with
  | .tokenLit "import" =>
    withErr "unfinised import statement" curr.pos imprt
  | .tokenLit "from" =>
    withErr "unfinished import statement" curr.pos fromImprt
  | _ => fail
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


namespace _Debug

def str := "import a.b.c as b"
-- #eval run str "<input>"

end _Debug
