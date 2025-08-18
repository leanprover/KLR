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
import Std.Data.HashMap.Basic

namespace KLR.Py.Parser

open Tokenizer (Token TokenKind)

def TokenMap (α : Type) := @Std.HashMap TokenKind α ⟨TokenKind.kindEq⟩ ⟨TokenKind.hash⟩

def TokenMap.emptyWithCapacity {α} (c : Nat) : TokenMap α :=
  @Std.HashMap.emptyWithCapacity TokenKind α ⟨TokenKind.kindEq⟩ ⟨TokenKind.hash⟩ c

instance {α} : Singleton (TokenKind × α) (TokenMap α) where
  singleton a := (TokenMap.emptyWithCapacity 8).insert a.1 a.2

instance {α} : Insert (TokenKind × α) (TokenMap α) where
  insert a m := m.insert a.1 a.2

structure Context where
  input    : Array Token
  fileInfo : FileInfo

structure State where
  ptr : Nat         := 0
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

def getInput : ParserM (Array Token) :=
  return (← read).input

def getTkPtr : ParserM Nat :=
  return (← get).ptr

def getPos! : ParserM Pos := do
  let input ← getInput
  let i ← getTkPtr
  if h : i < input.size then
    return input[i].pos
  else
    let some last := input.back? | fail
    return last.pos

def getStopPos : ParserM String.Pos := do
  let curr := (← getInput)[(← getTkPtr) - 1]?
  let pos  := curr.map (Pos.stopPos ∘ Token.pos)
  return pos.getD 0

def mkPosStartingAt (pos : Pos) : ParserM Pos := do
  let startPos := pos.pos
  let stopPos  ← getStopPos
  return ⟨startPos, if stopPos ≤ startPos then pos.stopPos else stopPos⟩

def clearErr : ParserM Unit :=
  modifyGet fun s => ((), {s with err := []})

def peekAt (i : Nat) : ParserM (Option Token) :=
  return (← read).input[i]?

def peek : ParserM (Option Token) := do
  peekAt (← getTkPtr)

def consume : ParserM Unit :=
  modifyGet fun s => ((), {s with ptr := s.ptr + 1})

def withPos {α β} (f : Pos → α → β) (p : ParserM α) : ParserM β := do
  let some curr ← peek | fail
  let i ← getTkPtr
  let a ← p
  let j ← getTkPtr
  if i ≥ j then pushErr "internal error: failed to get position infomataion" curr.pos; fail else
  let some last ← peekAt (j - 1) | pushErr "internal error: failed to get position information" curr.pos; fail
  return f ⟨curr.pos.pos, last.pos.stopPos⟩ a

def withErr {α} (msg : String) (pos? : Option Pos) (p : ParserM α) : ParserM α :=
  let pos := if h : pos?.isSome then pure (pos?.get h) else getPos!
  pos >>= fun pos => fun c s =>
  let (a?, s') := p c s
  match a? with
  | some a => return (a, s')
  | none =>
    let lastPos := Token.pos <$> c.input[s'.ptr - 1]? |> (Option.getD · pos)
    let msg := c.formatError msg ⟨pos.pos, lastPos.stopPos⟩
    (none, {s with err := msg :: s'.err})

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
  match c.input[s.ptr]? with
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
    let (a?, s') := p c {s with ptr := i}
    match a? with
    | some a =>
      let arr := arr.push a
      if s'.ptr ≤ i then ((arr, i), {s' with ptr := i}) else
      if s'.ptr ≥ input.size then ((arr, s.ptr), s') else
      go arr s'.ptr c s'
    | none => ((arr, i), {s with err := s'.err})
  termination_by input.size - i
  Prod.fst <$> go #[] (← getTkPtr)

def many1 {α} (p : ParserM α) : ParserM (Array α) := do
  let hd ← p
  let tl ← many p
  return #[hd] ++ tl

def optional {α} (p : ParserM α) : ParserM (Option α) := fun c s =>
  let (a?, s') := p c s
  match a? with
  | some a => (some (some a), s')
  | none   => (some none    , {s with err := s'.err})

def sepBy1 {α β} (p : ParserM α) (sep : ParserM β) (allowTrailing : Bool := true) : ParserM (Array α) := do
  let fst ← p
  let rst ← many (sep >> p)
  if allowTrailing then _ ← optional sep
  let rst := Prod.snd <$> rst
  return #[fst] ++ rst

def sepBy {α β} (p : ParserM α) (sep : ParserM β) (allowTrailing : Bool := true) : ParserM (Array α) :=
  (fun as => as.getD #[]) <$> optional (sepBy1 p sep allowTrailing)

def mkTokenMap {α} (l : List (String × α)) : TokenMap α :=
  let l := l.map fun (t, a) => (.tokenLit t, a)
  l.foldl
    (fun s (t, a) => s.insert t a)
    (.emptyWithCapacity l.length)

def token (s : String) : ParserM Unit := do
  let some ⟨.tokenLit curr, _⟩ ← peek | fail
  if curr == s then consume else fail

def newline : ParserM Unit := do
  let some ⟨.newline, _⟩ ← peek | fail
  consume

def indent : ParserM Unit := do
  let some ⟨.indent, _⟩ ← peek | fail
  consume

def dedent : ParserM Unit := do
  let some ⟨.dedent, _⟩ ← peek | fail
  consume

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
  | .l | .n => n | .r => n - 1

def unaryOpMap : TokenMap (Nat × UnaryOp) :=
  mkTokenMap [
    ("-"  , (100, .neg       )),
    ("+"  , (100, .pos       )),
    ("~"  , (100, .bitwiseNot)),
    ("not", (55 , .lnot      )),
  ]

def binOpMap : TokenMap (Nat × Assoc × BinOp) :=
  mkTokenMap [
    ("**" , (95, .r, .pow       )),
    ("*"  , (90, .l, .mul       )),
    ("@"  , (90, .l, .matmul    )),
    ("/"  , (90, .l, .div       )),
    ("//" , (90, .l, .floor     )),
    ("%"  , (90, .l, .mod       )),
    ("+"  , (85, .l, .add       )),
    ("-"  , (85, .l, .sub       )),
    ("<<" , (80, .l, .lshift    )),
    (">>" , (80, .l, .rshift    )),
    ("&"  , (75, .l, .bitwiseAnd)),
    ("^"  , (70, .l, .bitwiseXor)),
    ("|"  , (65, .l, .bitwiseOr )),
    (">=" , (60, .n, .ge        )),
    (">"  , (60, .n, .gt        )),
    ("<=" , (60, .n, .le        )),
    ("<"  , (60, .n, .lt        )),
    ("!=" , (60, .n, .ne        )),
    ("==" , (60, .n, .eq        )),
    ("and", (50, .l, .land      )),
    ("or" , (45, .l, .lor       )),
  ]

def precErr (pos : Pos) (nonAssoc : Bool := false) : ParserM Unit := do
  clearErr
  if nonAssoc then
    pushErr "chaining of comparison operators is not allowed" pos
  else
    pushErr "precedence level is low, consider parentheses" pos

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
    (.ident    ""     , withPos .mk <| Exp'.var <$> name),
    (.int      0      , withPos .mk <| numLit),
    (.float    0      , withPos .mk <| numLit),
    (.tokenLit "None" , withPos .mk <| (fun () => .value .none)         <$> consume),
    (.tokenLit "True" , withPos .mk <| (fun () => .value (.bool true )) <$> consume),
    (.tokenLit "False", withPos .mk <| (fun () => .value (.bool false)) <$> consume),
    (.string   ""     , withPos .mk <| strLit),
    (.tokenLit "("    ,                tuple),
    (.tokenLit "["    ,                list)
  }
  let some curr ← peek | fail
  let some p := atomMap.get? curr.kind | fail
  p

partial def arg : ParserM Arg := do
  let keyword ← optional (name >> token "=")
  let keyword := Prod.fst <$> keyword
  let val ← exp
  return { keyword, val }

partial def index : ParserM Index := do
  let l ← optional exp
  let some _ ← optional (token ":") | {
    let some l := l | fail
    return .coord l
  }
  let u ← optional exp
  let step ← optional (token ":" >> optional exp)
  let step := (Prod.snd <$> step).getD none
  return .slice l u step

/-- Assumes opening `[` is already matched -/
partial def typedCall : ParserM (List Exp × List Arg × String.Pos) := do
  consume
  let typs ← sepBy1 exp (token ",")
  _ ← token "]"
  _ ← token "("
  let args ← sepBy arg (token ",")
  let some ⟨.tokenLit ")", pos⟩ ← peek | fail
  consume
  return (typs.toList, args.toList, pos.stopPos)

/-- Assumes opening `[` is already matched -/
partial def indices : ParserM (List Index × String.Pos) := do
  consume
  let indices ← sepBy index (token ",")
  let some ⟨.tokenLit "]", pos⟩ ← peek | fail
  consume
  return (indices.toList, pos.stopPos)

partial def exp (precLimit : Nat := 0) : ParserM Exp := do
  let some start ← peek | fail

  -- first parser unary ops and atoms
  let fst : Exp ←
    match unaryOpMap.get? start.kind with
    | some (prec, op) =>
      if prec + 1 ≤ precLimit then
        precErr start.pos; fail
      else
        consume; let lhs ← exp prec
        pure ⟨⟨start.pos.pos, lhs.pos.stopPos⟩, .unaryOp op lhs⟩
    | none => atom

  let mut lhs := fst
  let mut curr ← peek

  -- primary loop
  while h : curr.isSome do
    let ⟨.tokenLit t, pos⟩ := curr.get h | break
    match t with
    | "." =>
      if 110 ≤ precLimit then precErr pos; break else
      consume
      let some ⟨.ident field, pos⟩ ← peek
        | pushErr "expected field access using an identifier" pos; fail
      consume
      lhs := ⟨⟨lhs.pos.pos, pos.stopPos⟩, .attr lhs field⟩
    | "(" =>
      if 110 ≤ precLimit then precErr pos; break else
      consume
      let args ← sepBy arg (token ",")
      let some ⟨.tokenLit ")", pos⟩ ← peek
        | pushErr "missing ) after function arguments" pos; fail
      consume
      lhs := ⟨⟨lhs.pos.pos, pos.stopPos⟩, .call lhs [] args.toList⟩
    | "[" =>
      if 110 ≤ precLimit then precErr pos; break else
      match ← optional typedCall with
      | some (typs, args, stopPos) =>
        lhs := ⟨⟨lhs.pos.pos, stopPos⟩, .call lhs typs args⟩
      | none =>
        let (indices, stopPos) ← indices
        if let some ⟨.tokenLit "(", pos⟩ ← peek then
          pushErr "please parenthesize calling a subscript expression, or it will be parsed as a generic function call" ⟨lhs.pos.pos, pos.stopPos⟩
          fail
        else
          lhs := ⟨⟨lhs.pos.pos, stopPos⟩, .access lhs indices⟩
    | _ => break
    curr ← peek

  -- binary-op/if-expression loop
  let mut precLimit := precLimit
  while h : curr.isSome do
    let tk := curr.get h
    match binOpMap.get? tk.kind with
    | some (prec, assoc, op) =>
      if prec ≤ precLimit then
        precErr tk.pos (assoc == .n); break
      else
        consume
        let rhs ← withErr "expected expression" tk.pos (exp (assoc.prec prec))
        lhs := ⟨⟨start.pos.pos, rhs.pos.stopPos⟩, .binOp op lhs rhs⟩
        if assoc == .n then precLimit := prec + 1
    | none =>
      let ⟨.tokenLit "if", _⟩ := tk | break
      if 40 ≤ precLimit then
        precErr tk.pos; break
      else
        consume; clearErr
        let cond ← withErr "unfinished if-expression" tk.pos (exp 40)
        _ ← withErr "missing else branch in if-expression" tk.pos (token "else")
        let els ← withErr "failed to pasrse else branch in if-expression" tk.pos (exp 39)
        lhs := ⟨⟨start.pos.pos, els.pos.stopPos⟩, .ifExp cond lhs els⟩
    curr ← peek

  return lhs

end

mutual

partial def patternAtom : ParserM Pattern := do
  let some _ ← optional (token "(")
    | Pattern.var <$> name
  let pat ← pattern
  _ ← token ")"
  return pat

partial def pattern : ParserM Pattern := do
  let hd ← patternAtom
  let some _ ← optional (token ",") | return hd
  let tl ← sepBy pattern (token ",")
  return .tuple (hd :: tl.toList)

end

def exps : ParserM Exp := do
  let hd ← exp
  let some ⟨.tokenLit ",", pos⟩ ← peek | return hd
  consume
  let tl ← sepBy exp (token ",")
  let lastPos := tl.back?.map (Pos.stopPos ∘ Exp.pos)
  let lastPos := lastPos.getD pos.stopPos
  return ⟨⟨hd.pos.pos, lastPos⟩, .tuple (hd :: tl.toList)⟩

def dottedName : ParserM QualifiedIdent := do
  not (token ".") "implicit current directory not supported"
  let ids ← sepBy1 name (token ".") false
  not (token ".") "did you accidentally left an extra '.' here?"
  return (ids.pop.toList, ids.back!)

def asName : ParserM (Option Ident) := do
  let as ← optional (token "as" >> name)
  not (token "as") "missing qualifier after 'as'"
  return Prod.snd <$> as

/-- Assumes the `import` keyword is already matched -/
def imprt : ParserM Stmt' := do
  let startPos ← getPos!
  consume
  let mod ← withErr "unfinished import statement" startPos dottedName
  not (token "from") "did you meant to do 'from ... import ...' ?"
  let as ← asName
  return .imprt mod as

/-- Assumes the `from` keyword is already matched -/
def fromImprt : ParserM Stmt' := do
  let startPos ← getPos!
  consume
  let mod ← withErr "unfinished import statement" startPos dottedName
  _ ← token "import"
  not (token "*") "import all not supported"
  let imp ← name
  not (token ".") "cannot qualify imports after from"
  let as ← asName
  return .imprtFrom mod imp as

/-- Assumes the `return` keyword is already matched -/
def returnStmt : ParserM Stmt' := do
  let startPos ← getPos!
  consume
  let exp? ← optional exp
  let exp := exp?.getD ⟨startPos, .value .none⟩
  return .ret exp

/-- Assumes the `assert` keyword is already matched -/
def assertStmt : ParserM Stmt' := do
  consume
  let exp ← exp
  return .assert exp

def simpleStmtMap : TokenMap (ParserM Stmt') := mkTokenMap [
  ("import"  , imprt                                       ),
  ("from"    , fromImprt                                   ),
  ("return"  , returnStmt                                  ),
  ("assert"  , assertStmt                                  ),
  ("pass"    , (Function.const _ .pass)         <$> consume),
  ("break"   , (Function.const _ .breakLoop)    <$> consume),
  ("continue", (Function.const _ .continueLoop) <$> consume)
]

def simpleStmt : ParserM Stmt := withPos .mk do
  let some curr ← peek | fail
  (simpleStmtMap.get? curr.kind).getD do
  -- parse assignment or expressions
  let lhs ← exps
  let anno := Prod.snd <$> (← optional (token ":" >> exp))
  let some ((), rhs) ← optional (token "=" >> exps) | {
    if h : anno.isSome then
      pushErr "uninitialized variables are not allowed" (anno.get h).pos
      fail
    else
      return .exp lhs
  }
  return .assign lhs anno rhs

def simpleStmts : ParserM (Array Stmt) :=
  Prod.fst <$>
    (sepBy1 simpleStmt (token ";")
      >> withErr "please insert a newline  after simple statements" none newline)

def decorator : ParserM Exp :=
  (Prod.fst ∘ .snd) <$> (token "@" >> exp >> newline)

def typParams : ParserM (List Ident) :=
  (·.2.1.toList) <$> (token "[" >> sepBy1 name (token ",") >> token "]")

def param : ParserM Param := do
  let keyword ← name
  let typ := Prod.snd <$> (← optional (token ":" >> exp))
  let dflt := Prod.snd <$> (← optional (token "=" >> exp))
  return { name := keyword, typ, dflt }

def params : ParserM (List Param) :=
  (·.2.1.toList) <$> (token "(" >> sepBy param (token ",") >> token ")")

mutual

partial def funcDef : ParserM Stmt' := do
  let decorators := (← many decorator).toList
  _ ← token "def"
  let n ← name
  let typParams := (← optional typParams).getD []
  let params ← params
  let returns := Prod.snd <$> (← optional (token "->" >> exp))
  _ ← token ":"
  let body ← block
  return .funcDef { decorators, name := n, typParams, params, returns, body }

/-- Assumes the `if` token is already matched -/
partial def ifStmt : ParserM Stmt' := do
  consume
  let cond ← exp
  _ ← token ":"
  let thn ← block
  let elifs :=
    (fun ((), cond, (), body) => (cond, body))
      <$> (← many <| token "elif" >> exp >> token ":" >> block)
  let els := (·.2.2) <$> (← optional <| token "else" >> token ":" >> block)
  return .ifStm cond thn elifs.toList els

/-- Assumes the `for` token is already matched -/
partial def forStmt : ParserM Stmt' := do
  (fun ((), pat, (), iter, (), body) => .forLoop pat iter body) <$>
  (consume >> pattern >> token "in" >> exps >> token ":" >> block)

/-- Assumes the `while` token is already matched -/
partial def whileStmt : ParserM Stmt' := do
  (fun ((), cond, (), body) => .whileLoop cond body) <$>
  (consume >> exp >> token ":" >> block)

partial def compoundStmt : ParserM Stmt := withPos .mk do
  let m := mkTokenMap [
    ("@"    , funcDef  ),
    ("def"  , funcDef  ),
    ("if"   , ifStmt   ),
    ("for"  , forStmt  ),
    ("while", whileStmt),
  ]
  let some curr ← peek | fail
  let some p := m.get? curr.kind | fail
  let r ← p
  return r

partial def statements1 : ParserM (List Stmt) := do
  (Array.toList ∘ Array.flatten) <$>
  (many1 (
    (Array.singleton <$> compoundStmt)
      <|> simpleStmts))

partial def block : ParserM (List Stmt) :=
  (·.2.2.1) <$> (newline >> indent >> statements1 >> dedent)
  <|> Array.toList <$> simpleStmts

end

def statements : ParserM (List Stmt) := do
  (·.getD []) <$> optional statements1

def run (input : String) (fileName : String) (fileMap : Lean.FileMap := input.toFileMap) : Except String Prog := do
  let tks ← Tokenizer.run input fileName fileMap
  let c : Context := {
    input := tks,
    fileInfo := {
      content := input,
      fileName,
      fileMap
    }
  }
  let (stmts?, s) := statements c {}
  let some stmts := stmts? | .error (s.err.getLast?.getD "invalid syntax")
  if h : s.ptr < tks.size then
    .error (s.err.getLast?.getD (c.formatError "invalid syntax" tks[s.ptr].pos))
  else
    .ok ⟨fileName, stmts⟩
