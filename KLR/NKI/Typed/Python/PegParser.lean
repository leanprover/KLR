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

namespace PegParser

/--
`τ` is the type of tokens with semantic value `T : (t : τ) → Type`

`ν` is the type of non-terminals with semantic value `N : (n : ν) → Type`
-/
inductive PExp (τ ν : Type) (T : τ → Type) (N : ν → Type) : Type → Type 1
  | empty : PExp τ ν T N Unit
  | token (t : τ) : PExp τ ν T N (T t)
  | prod (n : ν) : PExp τ ν T N (N n)
  | seq {α β : Type} (e1 : PExp τ ν T N α) (e2 : PExp τ ν T N β) : PExp τ ν T N (α × β)
  | choice {α : Type} (e1 : PExp τ ν T N α) (e2 : PExp τ ν T N α) : PExp τ ν T N α
  | star {α : Type} (e : PExp τ ν T N α) : PExp τ ν T N (List α)
  | not {α : Type} (e : PExp τ ν T N α) : PExp τ ν T N Unit
  | action {α β : Type} (e : PExp τ ν T N α) (f : α → β) : PExp τ ν T N β
  | leadingPrec {α : Type} (p : Nat) (e : PExp τ ν T N α) : PExp τ ν T N α
  | trailingPrec {α : Type} (l r : Nat) (e : PExp τ ν T N α) : PExp τ ν T N α
  | withPos {α β : Type} (e : PExp τ ν T N α) (f : α → String.Pos → String.Pos → β) : PExp τ ν T N β
  | invalid {α β : Type} (e : PExp τ ν T N α) (msg : String) : PExp τ ν T N β

abbrev Production (τ ν : Type) (T : τ → Type) (N : ν → Type) := (n : ν) → PExp τ ν T N (N n)

structure Context (τ ν : Type) (T : τ → Type) (N : ν → Type) where
  input      : Array τ
  tkEq       : τ → τ → Bool
  tkEq_sound : ∀ t1 t2 : τ, tkEq t1 t2 = true → T t1 = T t2
  tkData     : (t : τ) → T t
  tkStartPos : τ → String.Pos
  tkEndPos   : τ → String.Pos
  tkToString : τ → String
  errFormat  : String → String.Pos → String.Pos → String

def maxPrec := 1024

structure State where
  prec : Nat := maxPrec
  pos : Nat := 0
  err : List String := []

def State.pushErr (e : String) (s : State) : State :=
  {s with err := e :: s.err}

def State.next (s : State) : State :=
  {s with pos := s.pos + 1}

def State.pullErr (s1 : State) (s2 : State) : State :=
  {s1 with err := s2.err}
infix:100 "err<<" => State.pullErr

/--
A monadic setup doesn't buy us much here, since we require fine-grained control
over how the state is evolved and how results are intepreted.
-/
abbrev Parser (τ ν : Type) (T : τ → Type) (N : ν → Type) (α : Type) :=
  Context τ ν T N → State → Option α × State

section
variable {τ ν : Type} {T : τ → Type} {N : ν → Type}

namespace PExp

partial def parse {α} (e : PExp τ ν T N α) (prods : Production τ ν T N) : Parser τ ν T N α := fun c s =>
  match e with
  | .empty => ((), s)
  | .token t =>
    if let some curr := c.input[s.pos]? then
      if h : c.tkEq t curr then
        let d := c.tkEq_sound _ _ h ▸ c.tkData curr
        (d, s.next)
      else
        (none, s)
    else
      (none, s)
  | prod n => (prods n).parse prods c s
  | seq e1 e2 =>
    let (r1, s') := e1.parse prods c s
    match r1 with
    | some d1 =>
      let (r2, s') := e2.parse prods c s'
      match r2 with
      | .some d2 => ((d1, d2), s')
      | .none => (none, s err<< s')
    | none => (none, s err<< s')
  | choice e1 e2 =>
    let (r1, s') := e1.parse prods c s
    match r1 with
    | some d1 => (d1, s')
    | none => e2.parse prods c (s err<< s')
  | star e =>
    let (r, s') := e.parse prods c s
    match r with
    | some hd =>
      let (tl, s') := (star e).parse prods c s'
      let tl := tl.getD []
      ((hd :: tl), s')
    | _ => (some [], s err<< s')
  | not e =>
    let (r, s') := e.parse prods c s
    match r with
    | some _ => (none, s)
    | none   => ((), s err<< s')
  | action e f =>
    let (r, s') := e.parse prods c s
    match r with
    | some d  => ((f d), s')
    | none => (none, s err<< s')
  | leadingPrec prec e =>
    let savedPrec := s.prec
    let (r, s') := e.parse prods c {s with prec := prec}
    match r with
    | some d => (d, {s' with prec := savedPrec})
    | none => (none, s err<< s')
  | trailingPrec l r e =>
    let savedPrec := s.prec
    dbg_trace "prec tk={c.input[s.pos]?.map c.tkToString} l={l} r={r} saved={savedPrec}"
    if s.prec < savedPrec then (none, s.pushErr "low precedence, consider parenthesis") else
    let (r, s') := e.parse prods c {s with prec := r}
    match r with
    | some d => (d, {s' with prec := savedPrec})
    | none => (none, s err<< s')
  | withPos e f =>
    parseWithPos e (fun r s startPos endPos =>
      match r with
      | some d => ((f d startPos endPos), s)
      | none => (none, s)
    ) c s
  | invalid e msg =>
    parseWithPos e (fun r s startPos endPos =>
      match r with
      | some d =>
        let msg := c.errFormat msg startPos endPos
        (none, s.pushErr msg)
      | none => (none, s)
    ) c s
where
  parseWithPos {α β} (e : PExp τ ν T N α) (f : Option α → State → String.Pos → String.Pos → Option β × State) : Parser τ ν T N β := fun c s =>
    let i := s.pos
    if h : i ≥ c.input.size then (none, s) else
    let fst := c.input[i]
    let startPos := c.tkStartPos fst
    let (r, s') := e.parse prods c s
    let j := if s'.pos == i then i else s'.pos - 1
    match c.input[j]? with
    | some last =>
      f r s' startPos (c.tkEndPos last)
    | none =>
      let msg := c.errFormat "internal error, missing position information" startPos (c.tkEndPos fst)
      (none, s.pushErr msg)

def run (prods : Production τ ν T N) (start : ν) (c : Context τ ν T N) : Except String (N start) :=
  match (prods start).parse prods c {} with
  | (some d, s) =>
    -- dbg_trace "errs: [\n{"\n".intercalate s.err}\n]"
    if h : s.pos < c.input.size then
      let msg := s.err.getLastD <|
        let last := c.input[s.pos]
        let startPos := c.tkStartPos last
        let endPos := c.tkEndPos last
        c.errFormat "invalid syntax" startPos endPos
      .error msg
    else
      .ok d
  | (none, s) =>
    -- dbg_trace "errs: [\n{"\n".intercalate s.err}\n]"
    let msg := s.err.getLastD (
      match c.input[s.pos]? with
      | some tk =>
        let startPos := c.tkStartPos tk
        let endPos := c.tkEndPos tk
        c.errFormat "invalid syntax" startPos endPos
      | none => "invalid syntax"
    )
    .error msg

instance {α β} : HAndThen (PExp τ ν T N α) (PExp τ ν T N β) (PExp τ ν T N (α × β)) where
  hAndThen a b := PExp.seq a (b ())

instance {α} : OrElse (PExp τ ν T N α) where
  orElse a b := PExp.choice a (b ())

@[inline] def optional {α} (e : PExp τ ν T N α) : PExp τ ν T N (Option α) :=
  .action e some
  <|> .action .empty (fun _ => none)

@[inline] def and (e : PExp τ ν T N α) : PExp τ ν T N Unit :=
  .not <| .not e

def many1 {α} (e : PExp τ ν T N α) : PExp τ ν T N (List α) :=
  .action (e >> PExp.star e) fun (hd, tl) => hd :: tl

def sepBy1 {α β} (e : PExp τ ν T N α) (sep : PExp τ ν T N β) (allowTrailing := true) : PExp τ ν T N (List α) :=
  .action (
    e >> PExp.star (sep >> e) >>
      if allowTrailing then
        .action (optional sep) fun _ => ()
      else
        not sep
  ) fun (hd, tl, ()) => hd :: tl.map Prod.snd

@[inline] def sepBy {α β} (e : PExp τ ν T N α) (sep : PExp τ ν T N β) (allowTrailing := true) : PExp τ ν T N (List α) :=
  sepBy1 e sep allowTrailing
  <|> .action .empty (fun _ => [])

end PExp

end
