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
import KLR.NKI.Typed.Python.Tokenizer
import KLR.NKI.Typed.Python.Util

namespace KLR.NKI.Typed.Python.Parser

set_option grind.warning false

/-- Clears all hypotheses it can, except those provided after a minus sign. Example:
```
  clear * - h₁ h₂
```
-/
syntax (name := clearExcept) "clear " "*" " -" (ppSpace colGt ident)* : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| clear * - $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal ↦ do
      let mut toClear : Array FVarId := #[]
      for decl in ← getLCtx do
        unless fvarIds.contains decl.fvarId do
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
      goal.tryClearMany toClear

open Tokenizer (TokenKind Token)
open KLR.Core (Pos)
open Lean (FileMap)

instance : Add Pos where
  add x y := {
    line := x.line,
    column := x.column,
    lineEnd := y.lineEnd.getD y.line,
    columnEnd := y.columnEnd.getD y.column
  }

/-!
# Setup of parser types
-/

def NatGe (n : Nat) := {m : Nat // m ≥ n}

def NatGt (n : Nat) := {m : Nat // m > n}

structure Context where
  -- tokens   : Array Token
  fileName : String
  fileMap  : FileMap

structure State where
  err : Option String := none
  -- errStack  : List String   := []

/--
May not advace token position on success
-/
inductive ParseResult (α : Type) (n : Nat)
  | success (res : α) (m : NatGe n)
  | failure

/--
Must advace token position on success
-/
inductive ParseResultS (α : Type) (n : Nat)
  | success (res : α) (m : NatGt n)
  | failure

abbrev ParserM := ReaderT Context (EStateM String State)

abbrev ParserMR (α : Type) (n : Nat) := ParserM (ParseResult α n)

/--
Parser is a monad, but we cannot implement the standard library monad typeclass
because of the additional parameter `n` in the type of `ParserMR`.
To make `ParserMR` conform to `Type → Type`, we wound need to have `fun α => ParserMR α n`
for some additional fixed `n`.
-/
abbrev Parser (α : Type) := Array Token → (n : Nat) → ParserMR α n

abbrev ParserMRS (α : Type) (n : Nat) := ParserM (ParseResultS α n)

/--
Strictly progressing parser
-/
abbrev ParserS (α : Type) := Array Token → (n : Nat) → ParserMRS α n

instance : HasFileInfo ParserM where
  fileName := return (← read).fileName
  fileMap := return (← read).fileMap

/-!
# Utility functions
-/

instance {α n} : Coe (ParseResultS α n) (ParseResult α n) where
  coe
  | .success res ⟨next, _⟩ => .success res ⟨next, by omega⟩
  | .failure               => .failure

instance {α n} : Coe (ParserMRS α n) (ParserMR α n) := ⟨fun a => return ← a⟩

instance {α} : Coe (ParserS α) (Parser α) where
  coe a tks pos := do
    let res ← a tks pos
    pure res

def ParseResult.trans {α m n} (pr : ParseResult α m) (h : m ≥ n) : ParseResult α n :=
  match pr with
  | .success res ⟨pos, _⟩ => .success res ⟨pos, by omega⟩
  | .failure              => .failure

-- def getTokens : ParserM (Array Token) :=
--   return (← read).tokens

def succeed {α n} (res : α) (next : NatGe n) : ParserMR α n :=
  return .success res next

def succeedS {α n} (res : α) (next : NatGt n) : ParserMRS α n :=
  return .success res next

def next {α} (res : α) (n : Nat) : ParserMRS α n :=
  succeedS res ⟨n + 1, by simp⟩

def fail {α n} : ParserMR α n := do
  return .failure

def failS {α n} : ParserMRS α n := do
  return .failure

def mkErrMsg (msg : String) (tokens : Array Token) (pos : Nat) : ParserM String := do
  let (startPos, endPos) ←
    match tokens[pos]? with
    | some tk => pure (tk.pos, tk.endPos)
    | none    => pure ({}, {})
  formatError "SyntaxError" msg startPos endPos

def setErr (msg : String) : ParserM Unit := do
  let s ← get
  set {s with err := some msg}

def withErr {α} (msg : String) (p : Parser α) : Parser α := fun tks pos => do
  match ← p tks pos with
  | .success res next => succeed res next
  | .failure          => setErr (← mkErrMsg msg tks pos); fail

def withErrS {α} (msg : String) (p : ParserS α) : ParserS α := fun tks pos => do
  match ← p tks pos with
  | .success res next => succeedS res next
  | .failure          => setErr (← mkErrMsg msg tks pos); failS

def ParserS.map {α β : Type} (f : α → β) (p : ParserS α) : ParserS β := fun tks pos => do
  match ← p tks pos with
  | .success res next => succeedS (f res) next
  | .failure          => failS

instance : Functor ParserS where
  map := ParserS.map

def Parser.map {α β : Type} (f : α → β) (p : Parser α) : Parser β := fun tks pos => do
  match ← p tks pos with
  | .success res next => succeed (f res) next
  | .failure          => fail

instance : Functor Parser where
  map := Parser.map

-- def getTk? (n : Nat) : ParserM (Option Token) :=
--   return (← read).tokens[n]?

-- def getTk! {α m} (n : Nat) (k : Token → ParserMRS α m) : ParserMRS α m := do
--   let some tk ← getTk? n | failS
--   k tk

def throw {α} (msg : String) (tks : Array Token) (pos : Nat) : ParserM α := do
  let (startPos, endPos) :=
    match tks[pos]? with
    | some tk => (tk.pos, tk.endPos)
    | none    => ({},     {})
  let msg ← formatError "SyntaxError" msg startPos endPos
  MonadExcept.throw msg

def throwInternal {α} (msg : String) (tks : Array Token) (pos : Nat) : ParserM α := do
  throw s!"unexpected internal error, please report!\n{msg}" tks pos

def toPos (startPos endPos : String.Pos) : ParserM Pos := do
  let fileMap := (← read).fileMap
  let { line, column } := fileMap.toPosition startPos
  let { line := lineEnd, column := columnEnd } := fileMap.toPosition endPos
  pure { line, column, lineEnd, columnEnd }

instance {α} : OrElse (Parser α) where
  orElse a b tks pos := do
    match ← a tks pos with
    | .success res next => succeed res next
    | .failure          => b () tks pos

instance {α β} : HAndThen (Parser α) (Parser β) (Parser (α × β)) where
  hAndThen a b tks pos := do
    let .success fst ⟨next, _⟩ ← a tks pos     | fail
    let .success snd ⟨next, _⟩ ← b () tks next | fail
    succeed (fst, snd) ⟨next, by omega⟩

instance {α} : OrElse (ParserS α) where
  orElse a b tks pos := do
    match ← a tks pos with
    | .success res next => succeedS res next
    | .failure          => b () tks pos

instance {α β} : HAndThen (ParserS α) (ParserS β) (ParserS (α × β)) where
  hAndThen a b tks pos := do
    let .success fst ⟨next, _⟩ ← a tks pos     | failS
    let .success snd ⟨next, _⟩ ← b () tks next | failS
    succeedS (fst, snd) ⟨next, by omega⟩

instance {α β} : HAndThen (ParserS α) (Parser β) (ParserS (α × β)) where
  hAndThen a b tks pos := do
    let .success fst ⟨next, _⟩ ← a tks pos     | failS
    let .success snd ⟨next, _⟩ ← b () tks next | failS
    succeedS (fst, snd) ⟨next, by omega⟩

instance {α β} : HAndThen (Parser α) (ParserS β) (ParserS (α × β)) where
  hAndThen a b tks pos := do
    let .success fst ⟨next, _⟩ ← a tks pos     | failS
    let .success snd ⟨next, _⟩ ← b () tks next | failS
    succeedS (fst, snd) ⟨next, by omega⟩

def optionalS {α} (p : ParserS α) : Parser (Option α) := fun tks pos => do
  match ← p tks pos with
  | .success res ⟨next, _⟩ => succeed (some res) ⟨next, by omega⟩
  | .failure               => succeed none       ⟨pos, by simp⟩

def optional {α} (p : Parser α) : Parser (Option α) := fun tks pos => do
  match ← p tks pos with
  | .success res ⟨next, _⟩ => succeed (some res) ⟨next, by omega⟩
  | .failure               => succeed none       ⟨pos, by simp⟩

def many {α} (p : ParserS α) : Parser (Array α) := fun tks pos => do
  go #[] tks pos
where
  go (arr : Array α) : Parser (Array α) := fun tks pos => do
    match ← p tks pos with
    | .success res ⟨next, _⟩ =>
      let arr' := arr.push res
      if htokens : next ≥ tks.size then succeed arr' ⟨next, by omega⟩ else
      match ← go arr' tks next with
      | .success res ⟨next, _⟩ => succeed res ⟨next, by omega⟩
      | .failure               => succeed arr' ⟨next, by omega⟩
    | .failure => succeed arr ⟨pos, by simp⟩
  termination_by tks pos => tks.size - pos

def many1 {α} (p : ParserS α) : ParserS (Array α) := fun tks pos => do
  let .success fst ⟨pos, _⟩ ← p tks pos | failS
  let .success rst ⟨pos, _⟩ ← many p tks pos | throwInternal "`many` should not fail" tks pos
  succeedS (#[fst] ++ rst) ⟨pos, by omega⟩

/--
Try to match the current token' kind with `tk`
-/
def token? (tk : TokenKind) : Parser Bool := fun tks pos => do
  match tks[pos]? with
  | some curr =>
    if curr.kind == tk then
      let sPos ← toPos curr.pos curr.endPos
      next true pos
    else
      succeed false ⟨pos, by omega⟩
  | none => succeed false ⟨pos, by omega⟩

/--
Fails if the current token' kind is not equal to `tk`
-/
def token! (tk : TokenKind) : ParserS Unit := fun tks pos => do
  let some curr := tks[pos]? | failS
  if curr.kind == tk then
    next () pos
  else
    failS

def sepByAux {α} (p : ParserS α) (sep : Parser Bool) (arr : Array α) : Parser (Array α) := fun tks pos => do
  let .success res ⟨next, _⟩ ← p tks pos | succeed arr ⟨pos, by simp⟩
  let arr' := arr.push res
  if htokens : next ≥ tks.size then succeed arr' ⟨next, by omega⟩ else
  let .success true ⟨next, _⟩ ← sep tks next | succeed arr' ⟨next, by omega⟩
  let res ← sepByAux p sep arr' tks next
  pure <| res.trans (by omega)
termination_by tks pos => tks.size - pos

def sepBy {α} (p : ParserS α) (sep : TokenKind) : Parser (Array α) :=
  sepByAux p (token? sep) #[]

def sepBy1 {α} (p : ParserS α) (sep : TokenKind) : ParserS (Array α) := fun tks pos => do
  let sep := token? sep
  let .success fst  ⟨pos, _⟩ ← p tks pos                     | failS
  let .success true ⟨pos, _⟩ ← sep tks pos                   | succeedS #[fst] ⟨pos, by omega⟩
  let .success rest ⟨pos, _⟩ ← sepByAux p sep #[fst] tks pos | throwInternal "`sepBy` should never fail" tks pos
  succeedS rest ⟨pos, by omega⟩

def mkPos (startPos endPos : String.Pos) : ParserM Pos := toPos startPos endPos

def name : ParserS Ident := fun tks pos => do
  let some curr := tks[pos]? | failS
  let .ident name := curr.kind | failS
  next name pos

def type : ParserS Typ := fun tks pos => do
  if h : pos ≥ tks.size then failS else
  -- DO NOT IMPLEMENT THIS
  let curr := tks[pos]
  let startPos := curr.pos
  match curr.kind with
  | .ident "int" =>
    let endPos := curr.endPos
    let typ : Typ := ⟨← mkPos startPos endPos, .prim <| .numeric .int⟩
    next typ pos
  | .ident "float" =>
    let endPos := curr.endPos
    let typ : Typ := ⟨← mkPos startPos endPos, .prim <| .numeric .float⟩
    next typ pos
  | .ident id =>
    let endPos := curr.endPos
    let typ : Typ := ⟨← mkPos startPos endPos, .var id⟩
    next typ pos
  | _ => failS

def types : ParserS (List Typ) := fun tks pos => do
  let .success ts ⟨next, _⟩ ← sepBy1 type .comma tks pos | failS
  if h : next ≥ tks.size then failS else
  if tks[next].kind != .rbracket then failS else
  succeedS ts.toList ⟨next, by omega⟩

mutual

partial def atom : ParserS Exp := fun tks pos => do
  let some curr := tks[pos]? | failS
  let startPos := curr.pos
  match curr.kind with
  | .ident name =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .var name⟩ ⟨pos + 1, by omega⟩
  | .True =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value (.bool true)⟩ ⟨pos + 1, by omega⟩
  | .False =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value (.bool false)⟩ ⟨pos + 1, by omega⟩
  | .None =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value .none⟩ ⟨pos + 1, by omega⟩
  | .string value =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value (.string value)⟩ ⟨pos + 1, by omega⟩
  | .int value =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value (.int value)⟩ ⟨pos + 1, by omega⟩
  | .float value =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value (.float value)⟩ ⟨pos + 1, by omega⟩
  | .lparen =>
    let .success fst ⟨pos, _⟩ ← expression tks (pos + 1) | failS
    let ((exp, ⟨next, _⟩) : Exp × NatGe pos) ←
      match ← token! .comma tks pos with
      | .success () ⟨next, _⟩ =>
        let .success rest ⟨next, _⟩ ← sepBy expression .comma tks next
          | pure (⟨← mkPos startPos tks[next - 1]!.endPos, .tuple [fst]⟩, ⟨next, by omega⟩)
        pure (⟨← mkPos startPos tks[next - 1]!.endPos, .tuple (fst :: rest.toList)⟩, ⟨next, by omega⟩)
      | .failure => pure (fst, ⟨pos, by simp⟩)
    let .success () ⟨next, _⟩ ← token! .rparen tks next | failS
    succeedS exp ⟨next, by omega⟩
  | .lbracket =>
    let .success exps ⟨next, _⟩ ← sepBy expression .comma tks (pos + 1) | throwInternal "`sepBy` shoud not fail" tks pos
    let .success () ⟨next, _⟩ ← token! .rbracket tks next | failS
    let endPos := tks[next - 1]!.endPos
    succeedS ⟨← mkPos startPos endPos, .list exps.toList⟩ ⟨next, by omega⟩
  | .ellipsis =>
    let endPos := curr.endPos
    succeedS ⟨← mkPos startPos endPos, .value .ellipsis⟩ ⟨pos + 1, by omega⟩
  | _ => failS

/--
Manual Pratt Parser for expressions
-/
partial def expr (precLimit : Nat) : ParserS Exp := fun tks startPos => do
  if h : startPos ≥ tks.size then failS else
  -- parse unary prefixes and atoms first
  let curr := tks[startPos]
  let ((fst, ⟨pos, _⟩) : Exp × NatGt startPos) ←
    match curr.kind with
    | .minus =>
      if 100 ≤ precLimit then return .failure else
      let .success e ⟨next, _⟩ ← expr 99 tks (startPos + 1) | return .failure
      pure (⟨← mkPos curr.pos tks[next - 1]!.endPos, .unaryOp .neg e⟩, ⟨next, by omega⟩)
    | .plus =>
      if 100 ≤ precLimit then return .failure else
      let .success e ⟨next, _⟩ ← expr 99 tks (startPos + 1) | return .failure
      pure (⟨← mkPos curr.pos tks[next - 1]!.endPos, .unaryOp .pos e⟩, ⟨next, by omega⟩)
    | .tilde =>
      if 100 ≤ precLimit then return .failure else
      let .success e ⟨next, _⟩ ← expr 99 tks (startPos + 1) | return .failure
      pure (⟨← mkPos curr.pos tks[next - 1]!.endPos, .unaryOp .bitwiseNot e⟩, ⟨next, by omega⟩)
    | .not =>
      if 55 ≤ precLimit then return .failure else
      let .success e ⟨next, _⟩ ← expr 54 tks (startPos + 1) | return .failure
      pure (⟨← mkPos curr.pos tks[next - 1]!.endPos, .unaryOp .not e⟩, ⟨next, by omega⟩)
    | _ =>
      let .success atm next ← atom tks startPos | return .failure
      pure (atm, next)

  let mut prec : Nat := 0
  let mut left := fst
  let mut next : NatGe pos := ⟨pos, by simp⟩
  while h : next.val < tks.size do
    let ⟨next', _⟩ := next
    let curr := tks[next']
    let startPos := curr.pos
    match curr.kind with
    | .lbracket =>
      prec := 110
      if prec ≤ precLimit then break else
      let slices ← indices tks (next' + 1)
      let typArgs ← types tks (next' + 1)
      let ((newLeft, ⟨next'', h⟩) : Exp × NatGt (next' + 1)) ←
        match typArgs, slices with
        | .success typArgs ⟨typNext, ht⟩, .success slices ⟨sliceNext, hs⟩ =>
          -- both indexing and type applicaions match
          if h : typNext + 1 ≥ tks.size then
            -- access expression
            let endPos := tks[sliceNext]!.endPos
            pure (⟨← mkPos startPos endPos, .access left slices⟩, ⟨sliceNext + 1, by clear * - hs; grind⟩)
          else
            if tks[typNext + 1].kind != .lparen then
              -- access expression
              let endPos := tks[sliceNext]!.endPos
              pure (⟨← mkPos startPos endPos, .access left slices⟩, ⟨sliceNext + 1, by clear * - hs; grind⟩)
            else
              -- generic call
              let .success args ⟨next', ht'⟩ ← arguments tks (typNext + 2) | throwInternal "`arguments` should not fail" tks (typNext + 2)
              -- Note: `arguments` already checked that the next token is `)`
              let endPos := tks[next']!.endPos
              pure (⟨← mkPos startPos endPos, .call left typArgs args⟩, ⟨next' + 1, by clear * - ht ht'; grind⟩)
        | .success typArgs ⟨typNext, ht⟩, .failure =>
          -- generic call
          if h : typNext + 2 ≥ tks.size then break else
          if tks[typNext + 2].kind != .lparen then break else
          let .success args ⟨next', ht'⟩ ← arguments tks (typNext + 2) | throwInternal "`arguments` should not fail" tks (typNext + 2)
          -- Note: `arguments` already checked that the next token is `)`
          let endPos := tks[next']!.endPos
          pure (⟨← mkPos startPos endPos, .call left typArgs args⟩, ⟨next' + 1, by clear * - ht ht'; grind⟩)
        | .failure, .success slices ⟨sliceNext, hs⟩ =>
          -- access expression
          let endPos := tks[sliceNext]!.endPos
          if h : sliceNext + 1 ≥ tks.size then
            pure (⟨← mkPos startPos endPos, .access left slices⟩, ⟨sliceNext + 1, by clear * - hs; grind⟩)
          else if tks[sliceNext + 1].kind == .lparen then
            setErr "expected function application with type arguments, please consider parentheses"
            break
          else
            pure (⟨← mkPos startPos endPos, .access left slices⟩, ⟨sliceNext + 1, by clear * - hs; grind⟩)
        | .failure, .failure => break
      next := ⟨next'', by omega⟩
      left := newLeft
    | .lparen =>
      prec := 110
      if prec ≤ precLimit then break else
      let .success args ⟨next', _⟩ ← arguments tks (next' + 1) | throwInternal "`arguments` should never fail" tks next'
      if h : next' ≥ tks.size then break else
      if tks[next'].kind != .rparen then break else
      next := ⟨next' + 1, by omega⟩
      left := ⟨← mkPos startPos tks[next']!.endPos, .call left [] args⟩
    | .dot =>
      prec := 110
      if prec ≤ precLimit then break else
      if h : next' + 1 ≥ tks.size then break else
      let .ident id := tks[next' + 1].kind | break
      next := ⟨next' + 2, by omega⟩
      left := ⟨← mkPos startPos tks[next' + 1]!.endPos, .attr left id⟩
    | .dstar =>
      prec := 95
      if prec ≤ precLimit then break else
      let .success right ⟨next', _⟩ ← expr (prec - 1) tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .pow left right⟩
    | .star =>
      prec := 90
      if prec ≤ precLimit then break else
      let .success right ⟨next', _⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .mul left right⟩
    | .at =>
      prec := 90
      if prec ≤ precLimit then break else
      let .success right ⟨next', _⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .matmul left right⟩
    | .slash =>
      prec := 90
      if prec ≤ precLimit then break else
      let .success right ⟨next', _⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .div left right⟩
    | .dslash =>
      prec := 90
      if prec ≤ precLimit then break else
      let .success right ⟨next', _⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .floor left right⟩
    | .percent =>
      prec := 90
      if prec ≤ precLimit then break else
      let .success right ⟨next', _⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .mod left right⟩
    | .plus =>
      prec := 85
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .add left right⟩
    | .minus =>
      prec := 85
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .sub left right⟩
    | .lshift =>
      prec := 80
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .lshift left right⟩
    | .rshift =>
      prec := 80
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .rshift left right⟩
    | .amp =>
      prec := 75
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .bitwiseAnd left right⟩
    | .caret =>
      prec := 70
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .bitwiseXor left right⟩
    | .pipe =>
      prec := 65
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .bitwiseOr left right⟩
    | .ge =>
      prec := 60
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .ge left right⟩
    | .gt =>
      prec := 60
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .gt left right⟩
    | .le =>
      prec := 60
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .le left right⟩
    | .lt =>
      prec := 60
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .lt left right⟩
    | .ne =>
      prec := 60
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .ne left right⟩
    | .eq =>
      prec := 60
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .eq left right⟩
    | .and =>
      prec := 50
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .land left right⟩
    | .or =>
      prec := 50
      if prec ≤ precLimit then break else
      let .success right ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .binOp .lor left right⟩
    | .if =>
      prec := 40
      if prec ≤ precLimit then break else
      let .success cond ⟨next', h⟩ ← expr prec tks (next' + 1) | break
      if h : next' ≥ tks.size then break else
      if tks[next'].kind != .else then break else
      let .success els ⟨next', _⟩ ← expr (prec - 1) tks (next' + 1) | break
      next := ⟨next', by omega⟩
      left := ⟨← mkPos startPos tks[next' - 1]!.endPos, .ifExp cond left els⟩
    | _ => break
  succeedS left ⟨next.val, by have := next.property; omega⟩

partial def expression : ParserS Exp :=
  expr 0

partial def indices : ParserS (List Index) := fun tks pos => do
  let index : ParserS Index :=
    slice
    <|> (fun i => Index.coord i) <$> expression
  let .success idxes ⟨next, _⟩ ← sepBy1 index .comma tks pos | failS
  if h : next ≥ tks.size then failS else
  if tks[next].kind != .rbracket then failS else
  succeedS idxes.toList ⟨next, by omega⟩

partial def slice : ParserS Index :=
  (fun (l, (), opt) =>
    let (u, step) :=
      match opt with
      | some (u, some ((), step)) => (u   , step)
      | some (u, none)            => (u   , none)
      | none                      => (none, none)
    .slice l u step
  ) <$>
  (optionalS expression >> token! .colon
    >> optional (optionalS expression
      >> optionalS (token! .colon >> optionalS expression)))

partial def arguments : Parser (List Arg) := fun tks pos => do
  let .success args ⟨next, _⟩ ← sepBy arg .comma tks pos | throwInternal "`sepBy` should never fail" tks pos
  if h : next ≥ tks.size then fail else
  if tks[next].kind != .rparen then fail else
  succeed args.toList ⟨next, by omega⟩

partial def arg : ParserS Arg :=
  ((fun (keyword, (), val) => { keyword := some keyword, val })
  <$>
  (name >> token! .assign >> expression))
  <|>
  (fun val => { keyword := none, val })
  <$>
  expression

end

partial def expressions : ParserS Exp := fun tks pos => do
  let .success fst ⟨pos, _⟩ ← expression tks pos | failS
  match ← token! .comma tks pos with
  | .success () ⟨pos, _⟩ =>
    let .success rst ⟨pos, _⟩ ← sepBy expression .comma tks pos | throwInternal "`sepBy` should not fail" tks pos
    let sPos := if rst.isEmpty then fst.pos else fst.pos + rst.back!.pos
    succeedS ⟨sPos, .tuple (#[fst] ++ rst).toList⟩ ⟨pos, by omega⟩
  | .failure => succeedS fst ⟨pos, by omega⟩

partial def pattern : ParserS Pattern := fun tks pos => do
  if h : pos ≥ tks.size then failS else
  let curr := tks[pos]
  if curr.kind == .lparen then
    let .success fst ⟨next, _⟩ ← pattern tks (pos + 1) | failS
    if h : next ≥ tks.size then failS else
    let ((pat, ⟨last, _⟩) : Pattern × NatGt next) ←
      if tks[next].kind == .comma then
        let .success rest ⟨next, _⟩ ← sepBy pattern .comma tks (next + 1)
          | throwInternal "`sepBy` should never fail" tks (next + 1)
        pure <| (.tuple (#[fst] ++ rest).toList, ⟨next + 1, by omega⟩)
      else
        pure (fst, ⟨next + 1, by omega⟩)
    if h : last ≥ tks.size then failS else
    if tks[last].kind == .rparen then
      succeedS pat ⟨last + 1, by omega⟩
    else
      failS
  else
    let .ident id := curr.kind | failS
    succeedS (.var id) ⟨pos + 1, by omega⟩

def augassign : ParserS BinOp :=
      token .plusassign    .add
  <|> token .minusassign   .sub
  <|> token .starassign    .mul
  <|> token .atassign      .matmul
  <|> token .slashassign   .div
  <|> token .percentassign .mod
  <|> token .ampassign     .bitwiseAnd
  <|> token .pipeassign    .bitwiseOr
  <|> token .caretassign   .bitwiseXor
  <|> token .lshiftassign  .lshift
  <|> token .rshiftassign  .rshift
  <|> token .dstarassign   .pow
  <|> token .dslashassign  .floor
where
  token (tk : TokenKind) (op : BinOp) : ParserS BinOp :=
    (fun () => op) <$> token! tk

def assignment : ParserS Stmt :=
  ((fun (lhs, anno, (), rhs) =>
    let anno := anno.map Prod.snd
    -- TODO: fix pos here
    ⟨rhs.pos, .assign lhs anno rhs⟩
  ) <$> (
    expressions >> optionalS (token! .semicolon >> type) >> token! .assign >> expressions
  ))
  <|>
  ((fun (lhs, op, rhs) =>
    let pos := lhs.pos + rhs.pos
    ⟨pos, .assign lhs none ⟨pos, .binOp op lhs rhs⟩⟩
  ) <$> (expression >> augassign >> expression))

def dottedName : ParserS QualifiedIdent :=
  (fun (fst, rst) =>
    let rst := rst.map Prod.snd
    if h : rst.size = 0 then
      ([], fst)
    else
      let id    := rst.back
      let quals := fst :: rst.pop.toList
      (quals, id)
  )
  <$>
  (name >> many (token! .dot >> name))

def asName : Parser (Option Ident) :=
  Option.map Prod.snd <$>
  optionalS (token! .as >> name)

def importStmt : ParserS Stmt :=
  (fun ((), mod, (), imp, as) => /- TODO: pos -/ ⟨{}, .imprtFrom mod imp as⟩)
  <$>
  (token! .from >> dottedName >> token! .import >> name >> asName)

  <|>

  (fun ((), mod, as) => /- TODO: pos -/ ⟨{}, .imprt mod as⟩)
  <$>
  (token! .import >> dottedName >> asName)

def simpleStmt : ParserS Stmt :=
  assignment
  <|> (fun exp => ⟨exp.pos, .exp exp⟩) <$> expressions
  <|> (fun ((), exp) =>
        match exp with
        | some exp => ⟨exp.pos, .ret exp⟩
        | none =>
          /- TODO: fill in position -/
          ⟨{}, .ret ⟨{}, .value .none⟩⟩)
        <$> (token! .return >> optionalS expressions)
  <|> importStmt
  <|> token .pass
  <|> (fun ((), exp) => /- TODO: fix pos here -/ ⟨exp.pos, .assert exp⟩) <$> (token! .assert >> expression)
  <|> token .break
  <|> token .continue
where
  token (tk : TokenKind) : ParserS Stmt := fun tks pos => do
    let .success () ⟨pos, _⟩ ← token! tk tks pos | failS
    let stmt' : Option Stmt' :=
      match tk with
      | .pass => some .pass
      | .break => some .breakLoop
      | .continue => some .continueLoop
      | _ => none
    let some stmt' := stmt' | failS
    let sPos ← mkPos tks[pos - 1]!.pos tks[pos - 1]!.endPos
    succeedS ⟨sPos, stmt'⟩ ⟨pos, by omega⟩

def simpleStmts : ParserS (List Stmt) :=
  (fun (stmts, ()) => stmts.toList) <$>
    (sepBy1 simpleStmt .semicolon
      >> (withErrS "expected new line at the end of simple statements" <|
            token! .newline))

def decorators : Parser (List Exp) :=
  (fun decs => (decs.map (Prod.fst ∘ Prod.snd)).toList)
  <$>
  many (token! .at >> expression >> token! .newline)

def params : Parser (List Param) :=
  (fun params => (params.map fun (name, typ, dflt) => ⟨name, typ.map Prod.snd, dflt.map Prod.snd⟩).toList)
  <$>
  sepBy (name >> optionalS (token! .colon >> type) >> optionalS (token! .assign >> expression)) .comma

mutual

partial def functionDef : ParserS Stmt :=
  (fun (decorators, (), name, typParams, (), params, (), returns, (), body) =>
    let typParams := ((typParams.map (Prod.fst ∘ Prod.snd)).getD #[]).toList
    let returns := returns.map Prod.snd
    /- TODO: pos -/
    ⟨{}, .funcDef { decorators, name, typParams, params, returns, body }⟩
  )
  <$>
  (decorators >> token! .def
    >> withErrS "expected identifier" name
    >> optionalS (token! .lbracket >> sepBy1 name .comma >> token! .rbracket)
    >> withErrS "expected (" (token! .lparen)
    >> params
    >> withErrS "expected )" (token! .rparen)
    >> optionalS (token! .rarrow >> type)
    >> token! .colon >> block)

partial def ifStmt : ParserS Stmt :=
  (fun ((), cond, (), thn, elifs, els) =>
    let elifs := (elifs.map (fun ((), cond, (), thn) => (cond, thn))).toList
    let els := els.map (Prod.snd ∘ Prod.snd)
    /- TODO: pos -/
    ⟨{}, .ifStm cond thn elifs els⟩
  )
  <$>
  (token! .if >> expression >> token! .colon >> block
    >> many (token! .elif >> expression >> token! .colon >> block)
    >> optionalS (token! .else >> token! .colon >> block))

partial def forStmt : ParserS Stmt :=
  (fun ((), pat, (), iter, (), body) => /- TODO: pos -/ ⟨{}, .forLoop pat iter body⟩)
  <$>
  (token! .for >> pattern >> token! .in >> expression >> token! .colon >> block)

partial def whileStmt : ParserS Stmt :=
  (fun ((), cond, (), body) => /- TODO: pos -/ ⟨{}, .whileLoop cond body⟩)
  <$>
  (token! .while >> expression >> token! .colon >> block)

partial def compoundStmt : ParserS Stmt :=
  functionDef
  <|> ifStmt
  <|> forStmt
  <|> whileStmt

partial def statements1 : ParserS (List Stmt) :=
  (fun arr => arr.toList.flatten) <$>
  (withErrS "cannot have empty statements here" (many1 <| (List.singleton <$> compoundStmt) <|> simpleStmts))

partial def block : ParserS (List Stmt) :=
  ((fun ((), (), stmts, ()) => stmts) <$> (
    token! .newline >> token! .indent >> statements1 >> token! .dedent
  )) <|> simpleStmts

end

def statements : Parser (List Stmt) :=
  (fun arr => arr.toList.flatten) <$>
  (many <| (List.singleton <$> compoundStmt) <|> simpleStmts)

def run (input : String) (fileName : String := "<input>") (fileMap : FileMap := input.toFileMap)
  : Except String Prog := do
  let tokens ← Tokenizer.run input fileName fileMap
  match ((statements tokens 0).run { fileName, fileMap }).run {} with
  | .ok (.success res ⟨pos, _⟩) { err } =>
    if pos == tokens.size then .ok ⟨fileName, res⟩ else .error <| err.getD "Invalid Syntax"
  | .ok .failure { err }   => .error (err.getD "Invalid Syntax")
  | .error msg _           => .error msg
