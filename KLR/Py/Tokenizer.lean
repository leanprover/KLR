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
import KLR.Py.PosLemmas
import KLR.Py.Util

set_option grind.warning false

namespace KLR.Py.Tokenizer

/- https://docs.python.org/3/reference/lexical_analysis.html -/

open Lean (FileMap)

inductive TokenKind
  | ident    (name  : Ident)
  | int      (value : Int)
  | float    (value : Float)
  | string   (value : String)
  | tokenLit (value : String)
  | newline | indent | dedent
with
  @[computed_field] hash : TokenKind → UInt64
    | .ident    _ => String.hash "⟪ident⟫"
    | .int      _ => String.hash "⟪int⟫"
    | .float    _ => String.hash "⟪float⟫"
    | .string   _ => String.hash "⟪string⟫"
    | .tokenLit t => String.hash t
    | .newline    => String.hash "⟪newline⟫"
    | .indent     => String.hash "⟪indent⟫"
    | .dedent     => String.hash "⟪dedent⟫"
deriving Repr, Inhabited, BEq

def TokenKind.kindEq : TokenKind → TokenKind → Bool
  | .tokenLit x, .tokenLit y => x == y
  | .ident    _, .ident    _
  | .int      _, .int      _
  | .float    _, .float    _
  | .string   _, .string   _
  | .newline   , .newline
  | .indent    , .indent
  | .dedent    , .dedent     => true
  | _          , _           => false

scoped macro "tk" s:str : term =>
  `(TokenKind.tokenLit $s)

def TokenKind.toString : TokenKind → String
  | .ident    name   => name
  | .int      value  => s!"{value}"
  | .float    value  => s!"{value}"
  | .string   value  => s!"\"{value}\""
  | .tokenLit value  => value
  | .newline         => "NEWLINE"
  | .indent          => "INDENT"
  | .dedent          => "DEDENT"

instance instToStingTokenKind : ToString TokenKind := ⟨TokenKind.toString⟩

structure Token where
  kind   : TokenKind
  pos    : Pos
deriving Repr, Inhabited, BEq

structure State where
  tokens      : Array Token            := #[]
  indentStack : List Nat               := [0]
  /--
  Used to check implicit line joining
  https://docs.python.org/3/reference/lexical_analysis.html#implicit-line-joining
  -/
  bracesStack : List (TokenKind × Pos) := []

abbrev TokenizerM := ReaderT FileInfo (EStateM String State)

def throw {α} (msg : String) (pos : Pos) : TokenizerM α := do
  let msg := (← read).formatError "SyntaxError" msg pos
  monadLift (m := EStateM String State) (EStateM.throw msg)

def throwInternal {α} (pos : Pos) : TokenizerM α := do
  throw "unexpected internal error, please report!" pos

def indentLevel (errPos : Pos) : TokenizerM Nat := do
  let { indentStack, .. } ← get
  match indentStack.head? with
  | some n => pure n
  | none   => throwInternal errPos

def getInput : TokenizerM String :=
  return (← read).content

def pushToken (t : TokenKind) (pos : Pos) : TokenizerM Unit := do
  let s ← get
  set {s with tokens := s.tokens.push ⟨t, pos⟩}

def getBracesStack : TokenizerM (List (TokenKind × Pos)) := do
  pure (← get).bracesStack

def pushBrace (br : TokenKind) (pos : Pos) : TokenizerM Unit := do
  let s ← get
  set {s with bracesStack := (br, pos) :: s.bracesStack}

def popBrace : TokenizerM (Option (TokenKind × Pos)) := do
  let s ← get
  let stack := s.bracesStack
  set {s with bracesStack := stack.tail}
  pure stack.head?

def lineJoin : TokenizerM Bool := do
  pure !(← get).bracesStack.isEmpty

def isPythonWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == Char.ofNat 0x0C /- form feed -/

def newline (pos : String.Pos) (pushNewline : Bool := true) : TokenizerM (Option (PosGt pos)) := do
  let input ← getInput
  let str := input.extract pos (pos + ⟨3⟩)
  let next : Option (PosGt pos) :=
       if str.startsWith "\r\n" then some ⟨pos + "\r\n", String.add_gt (by simp_str_size)⟩
  else if str.startsWith "\r"   then some ⟨pos + "\r"  , String.add_gt (by simp_str_size)⟩
  else if str.startsWith "\n"   then some ⟨pos + "\n"  , String.add_gt (by simp_str_size)⟩
  else none
  match next with
  | some next =>
    if pushNewline && !(← lineJoin) then pushToken .newline ⟨pos, next.val⟩
    return next
  | none => return none

def pushIndent (pos : Pos) (n : Nat) : TokenizerM Unit := do
  let s ← get
  set {s with indentStack := n :: s.indentStack}
  pushToken .indent pos

def popIndent (pos : Pos) (n : Nat) : TokenizerM Unit := do
  let stack := (← get).indentStack
  let newStack ← go stack
  modifyGet fun s => ((), {s with indentStack := newStack})
where
  go : List Nat → TokenizerM (List Nat)
  | [] => throwInternal pos
  | hd :: tl => do
    if hd == n then
      pure (hd :: tl)
    else if hd > n then
      pushToken .dedent pos
      go tl
    else
      throw "inconsistent dedent" pos

def finishLineComment (pos : String.Pos) (pushNewline : Bool := true) : TokenizerM (PosGt pos) := do
  let input ← getInput
  let rec skip (pos : String.Pos) : TokenizerM (PosGt pos) := do
    if h : input.atEnd pos then return ⟨pos + ⟨1⟩, by simp⟩ else
    match ← newline pos pushNewline with
    | some next => return next
    | none =>
      have := String.lt_sub_next h
      let next ← skip (input.next' pos h)
      return next.fromNext'
  termination_by input.endPos.1 - pos.1
  return (← skip pos)

inductive CheckIndentResult (pos : String.Pos)
  | lineEmpty    (next : PosGt pos)
  | lineNotEmpty (next : PosGe pos)

def checkIndent (startPos : String.Pos) : TokenizerM (CheckIndentResult startPos) := do
  let input ← getInput
  let next := input.findAux (· != ' ') input.endPos startPos
  have hle : startPos.1 ≤ next.1 := String.findAux_le_start

  if h : input.atEnd next then return .lineEmpty ⟨next + ⟨1⟩, by grind only [String.Pos.add_byteIdx]⟩ else
  if let some next ← newline next false then return .lineEmpty <| next.fromLe hle

  let errPos : Pos := ⟨next, input.next' next h⟩
  match input.get' next h with
  | '#' =>
    let next ← finishLineComment next false
    return .lineEmpty <| next.fromLe hle
  | '\t' =>
    throw "tab indents not supported, please configure your editor to use spaces" errPos
  | _ =>
    let currIndent := (next - startPos).1
    let indent ← indentLevel errPos
    let pos : Pos := ⟨startPos, next⟩

    if currIndent > indent then
      pushIndent pos currIndent
    else if currIndent < indent then
      popIndent pos currIndent
    pure <| .lineNotEmpty ⟨next, hle⟩

@[inline] def throwUnmatchedBrace {α} (brace : TokenKind) (pos : Pos) : TokenizerM α := do
  throw s!"unmatched {brace}" pos

@[inline] def bracesMatch : TokenKind → TokenKind → Bool
  | tk"(", tk")"
  | tk"[", tk"]"
  | tk"{", tk"}" => true
  | _    , _     => false

def checkBraces (brace : TokenKind) (pos : Pos) : TokenizerM Unit := do
  match brace with
  | tk"(" | tk"{" | tk"[" =>
    pushBrace brace pos
  | tk")" | tk"}" | tk"]" =>
    match ← popBrace with
    | some (left, pos) =>
      if !bracesMatch left brace then
        throwUnmatchedBrace left pos
    | none =>
      throwUnmatchedBrace brace pos
  | _ => return

def opsAndDelimsLit : List {s : String // s.utf8ByteSize > 0} := [
  ⟨"...", by simp_str_size⟩,
  ⟨"<<=", by simp_str_size⟩,
  ⟨">>=", by simp_str_size⟩,
  ⟨"**=", by simp_str_size⟩,
  ⟨"//=", by simp_str_size⟩,
  ⟨"->" , by simp_str_size⟩,
  ⟨"*=" , by simp_str_size⟩,
  ⟨"/=" , by simp_str_size⟩,
  ⟨"%=" , by simp_str_size⟩,
  ⟨"+=" , by simp_str_size⟩,
  ⟨"-=" , by simp_str_size⟩,
  ⟨"@=" , by simp_str_size⟩,
  ⟨"&=" , by simp_str_size⟩,
  ⟨"|=" , by simp_str_size⟩,
  ⟨"^=" , by simp_str_size⟩,
  ⟨":=" , by simp_str_size⟩,
  ⟨"<<" , by simp_str_size⟩,
  ⟨">>" , by simp_str_size⟩,
  ⟨"**" , by simp_str_size⟩,
  ⟨"//" , by simp_str_size⟩,
  ⟨"==" , by simp_str_size⟩,
  ⟨"!=" , by simp_str_size⟩,
  ⟨"<=" , by simp_str_size⟩,
  ⟨">=" , by simp_str_size⟩,
  ⟨"<"  , by simp_str_size⟩,
  ⟨">"  , by simp_str_size⟩,
  ⟨"+"  , by simp_str_size⟩,
  ⟨"-"  , by simp_str_size⟩,
  ⟨"*"  , by simp_str_size⟩,
  ⟨"/"  , by simp_str_size⟩,
  ⟨"%"  , by simp_str_size⟩,
  ⟨"&"  , by simp_str_size⟩,
  ⟨"|"  , by simp_str_size⟩,
  ⟨"^"  , by simp_str_size⟩,
  ⟨"~"  , by simp_str_size⟩,
  ⟨"("  , by simp_str_size⟩,
  ⟨")"  , by simp_str_size⟩,
  ⟨"["  , by simp_str_size⟩,
  ⟨"]"  , by simp_str_size⟩,
  ⟨"{"  , by simp_str_size⟩,
  ⟨"}"  , by simp_str_size⟩,
  ⟨","  , by simp_str_size⟩,
  ⟨":"  , by simp_str_size⟩,
  ⟨"@"  , by simp_str_size⟩,
  ⟨"!"  , by simp_str_size⟩,
  ⟨"."  , by simp_str_size⟩,
  ⟨";"  , by simp_str_size⟩,
  ⟨"="  , by simp_str_size⟩,
]

def operatorAndDelimiter (startPos : String.Pos) : TokenizerM (Option (PosGt startPos)) := do
  let input ← getInput
  let subStr := input.extract startPos (startPos + ⟨3⟩)
  let res : Option (TokenKind × PosGt startPos) :=
    (opsAndDelimsLit.find? (fun s => subStr.startsWith s.val)).map
      (fun ⟨s, h⟩ => (.tokenLit s, ⟨startPos + s, String.add_gt h⟩))
  match res with
  | some (t, endPos) =>
    let pos := ⟨startPos, endPos⟩
    checkBraces t pos
    pushToken t pos
    return endPos
  | none => return none

def decodeStrEscape (pos : String.Pos) (s : String) : TokenizerM (String × PosGt pos) := do
  let input ← getInput
  match ← newline pos with
  | some ⟨pos, h⟩ =>
    return (s, ⟨pos, by omega⟩)
  | none => -- escape sequence
    if h : input.atEnd pos then throw "unterminated string literal" ⟨input.prev pos, pos⟩ else
    let curr := input.get' pos h
    let next := PosGt.next' pos h
    -- TODO: This is a subset of what's allowed from the Python spec
    match curr with
    | '\\'
    | '\"'
    | '\'' => pure (s.push curr        , next)
    | 'a'  => pure (s.push (.ofNat 0x7), next)
    | 'b'  => pure (s.push (.ofNat 0x8), next)
    | 'f'  => pure (s.push (.ofNat 0xc), next)
    | 'n'  => pure (s.push '\n'        , next)
    | 'r'  => pure (s.push '\r'        , next)
    | 't'  => pure (s.push '\t'        , next)
    | 'v'  => pure (s.push (.ofNat 0xb), next)
    | _    => throw "invalid escape sequence" ⟨pos, input.next' pos h⟩

def finishShortStr (pos : String.Pos) (doubleQuote : Bool) : TokenizerM (String × PosGt pos) := do
  let input ← getInput
  let firstQuote := if doubleQuote then '\"' else '\''
  let rec go (s : String) (pos : String.Pos) : TokenizerM (String × PosGt pos) := do
    if h : input.atEnd pos then throw "unterminated string literal" ⟨input.prev pos, pos⟩ else
    if let some ⟨next, _⟩ ← newline pos then throw "unterminated string literal" ⟨pos, next⟩ else

    let curr := input.get' pos h
    let ⟨next, hn⟩ := PosGt.next' pos h

    if curr == firstQuote then
      pure (s, ⟨next, hn⟩)
    else if curr == '\\' then
      let (s, ⟨endPos, _⟩) ← decodeStrEscape next s
      let (s, ⟨endPos, _⟩) ← go s endPos
      pure (s, ⟨endPos, by omega⟩)
    else
      let (s, ⟨endPos, _⟩) ← go (s.push curr) next
      pure (s, ⟨endPos, by omega⟩)
  termination_by input.endPos.1 - pos.1
  decreasing_by
    all_goals (have := String.lt_end h; omega)
  go "" pos

def finishLongStr (pos : String.Pos) (doubleQuote : Bool) : TokenizerM (String × PosGt pos) := do
  let input ← getInput
  let tquote := if doubleQuote then "\"\"\"" else "\'\'\'"
  let rec go (s : String) (pos : String.Pos) : TokenizerM (String × PosGt pos) := do
    if h : input.atEnd pos then throw "unterminated string literal" ⟨input.prev pos, pos⟩ else

    if tquote == input.extract pos (pos + tquote) then return (s, ⟨pos + tquote, String.add_gt (by
      simp only [tquote]; split <;> simp_str_size
    )⟩) else

    let curr := input.get' pos h
    let ⟨next, hn⟩ := PosGt.next' pos h

    if curr == '\\' then
      let (s, ⟨endPos, _⟩) ← decodeStrEscape next s
      let (s, ⟨endPos, _⟩) ← go s endPos
      pure (s, ⟨endPos, by omega⟩)
    else
      let (s, ⟨endPos, _⟩) ← go (s.push curr) next
      pure (s, ⟨endPos, by omega⟩)
  termination_by input.endPos.1 - pos.1
  decreasing_by
    all_goals (have := String.lt_end h; omega)
  go "" pos

def finishStr (pos : String.Pos) (doubleQuote : Bool) : TokenizerM (String × PosGt pos) := do
  let input ← getInput
  let dquote := if doubleQuote then "\"\"" else "\'\'"
  if input.extract pos (pos + dquote) == dquote then
    let next : PosGt pos := ⟨pos + dquote, String.add_gt (by simp only [dquote]; split <;> simp_str_size)⟩
    let (s, endPos) ← finishLongStr next doubleQuote
    pure (s, ⟨endPos.val, by omega⟩)
  else
    finishShortStr pos doubleQuote

def isIdFirst (c : Char) : Bool :=
  c.isAlpha || c == '_'

def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c == '_'

def finishIdent (pos : String.Pos) (first : Char) : TokenizerM (String × PosGe pos) := do
  let input ← getInput
  let next := input.findAux (!isIdRest ·) input.endPos pos
  let id := first.toString ++ (input.extract pos next)
  pure (id, ⟨next, String.findAux_le_start⟩)

def decodeNat (s : String) (errPos : Pos) : TokenizerM Nat := do
  match s.toNat? with
  | some n => pure n
  | none   => throw "invalid int literal" errPos

def decodeFloatAux (before after : String) : Option Float := do
  let mantissa ← before.toNat?
  let (mantissa, exponent) ← decodeAfter mantissa 0 after.toList
  Float.ofScientific mantissa true exponent
where
  decodeAfter (mantissa exponent : Nat) : List Char → Option (Nat × Nat)
  | [] => (mantissa, exponent)
  | hd :: tl =>
    if hd.isDigit then
      let hd := hd.toNat - '0'.toNat
      decodeAfter (mantissa * 10 + hd) (exponent + 1) tl
    else
      none

def decodeFloat (before after : String) (errPos : Pos) : TokenizerM Float := do
  match decodeFloatAux before after with
  | some float => pure float
  | none       => throw "invalid float literal" errPos

/--
TODO: Implement full python numeric literal with underscores and scientific notations
-/
def finishNum (pos : String.Pos) (first : Char) : TokenizerM (TokenKind × PosGe pos) := do
  let input ← getInput
  let extractDigits (pos : String.Pos) : String × PosGe pos :=
    let next := input.findAux (not ∘ Char.isDigit) input.endPos pos
    (input.extract pos next, ⟨next, String.findAux_le_start⟩)

  let (int, next) := extractDigits pos
  let int := first.toString ++ int
  let errPos : Pos := ⟨input.prev pos, next⟩
  if h : input.atEnd next then return (.int <| ← decodeNat int errPos, next) else

  let curr := input.get' next h
  if curr != '.' then return (.int <| ← decodeNat int errPos, next) else
  let ⟨next, _⟩ := PosGt.next' next h

  let (afterDot, ⟨next, _⟩) := extractDigits next
  let float ← decodeFloat int afterDot ⟨input.prev pos, next⟩
  return (.float float, ⟨next, by omega⟩)

/--
Ensure proper separation of a numeric literal with the next token for better error messages.
-/
def checkNumLitEnd (pos : Pos) : TokenizerM Unit := do
  let input ← getInput
  if h : input.atEnd pos.stopPos then return else
  let curr := input.get' pos.stopPos h
  if isIdRest curr then
    throw "invalid numeric literal" pos

def identKind (s : String) : TokenKind :=
  match s with
  | "False"
  | "await"
  | "else"
  | "import"
  | "pass"
  | "None"
  | "break"
  | "except"
  | "in"
  | "raise"
  | "True"
  | "class"
  | "finally"
  | "is"
  | "return"
  | "and"
  | "continue"
  | "for"
  | "lambda"
  | "try"
  | "as"
  | "def"
  | "from"
  | "nonlocal"
  | "while"
  | "assert"
  | "del"
  | "global"
  | "not"
  | "with"
  | "async"
  | "elif"
  | "if"
  | "or"
  | "yield" => .tokenLit s
  | id      => .ident id

def tokenizeLine (pos : String.Pos) : TokenizerM (PosGt pos) := do
  let input ← getInput
  let rec go (pos : String.Pos) : TokenizerM (PosGt pos) := do
    if h : input.atEnd pos then return ⟨pos + ⟨1⟩, by simp⟩ else

    if let some ⟨next, hn⟩ ← newline pos then
      if ← lineJoin then
        let ⟨next, _⟩ ← go next
        return ⟨next, by omega⟩
      else
        return ⟨next, hn⟩
    else

    let curr := input.get' pos h
    let ⟨next, _⟩ := PosGt.next' pos h

    let contGe (endPos : PosGe next) : TokenizerM (PosGt pos) := do
      let ⟨next, _⟩ ← go endPos
      pure ⟨next, by omega⟩

    let contGt (endPos : PosGt next) : TokenizerM (PosGt pos) := do
      let ⟨next, _⟩ ← go endPos
      pure ⟨next, by omega⟩

    if curr == '\\' then
      let some next ← newline next |
        throw "unexpected character after line continuation character" ⟨pos, next⟩
      contGt next
    else if curr == '#' then -- line comments
      let ⟨next, h⟩ ← finishLineComment next
      if ← lineJoin then
        contGt ⟨next, h⟩
      else
        return ⟨next, by omega⟩
    else if isPythonWhitespace curr then -- white space
      contGe ⟨next, by omega⟩
    else if curr.isDigit then -- numeric literal
      let (t, next) ← finishNum next curr
      checkNumLitEnd ⟨pos, next⟩
      pushToken t ⟨pos, next⟩
      contGe next
    else if curr == '\'' then
      let (str, next) ← finishStr next false
      pushToken (.string str) ⟨pos, next⟩
      contGt next
    else if curr == '\"' then
      let (str, next) ← finishStr next true
      pushToken (.string str) ⟨pos, next⟩
      contGt next
    else if isIdFirst curr then
      let (id, next) ← finishIdent next curr
      pushToken (identKind id) ⟨pos, next⟩
      contGe next
    else
      match ← operatorAndDelimiter pos with
      | some next =>
        let next ← go next
        return ⟨next, by omega⟩
      | none =>
        throw "unexpected character" ⟨pos, next⟩
  termination_by input.endPos.1 - pos.1
  decreasing_by
    all_goals (have := String.lt_sub_next h; omega)
  go pos

def tokenize : TokenizerM Unit := do
  let input ← getInput
  let rec go (pos : String.Pos) : TokenizerM (PosGt pos) := do
    if h : input.atEnd pos then pure ⟨pos + ⟨1⟩, by simp⟩ else
    match ← checkIndent pos with
    | .lineEmpty ⟨pos, _⟩ =>
      let ⟨res, _⟩ ← go pos
      return ⟨res, by omega⟩
    | .lineNotEmpty ⟨pos, _⟩ =>
      let ⟨next, _⟩ ← tokenizeLine pos
      if hgt : next.1 > pos.1 then
        let ⟨res, _⟩ ← go next
        pure ⟨res, by omega⟩
      else
        if input.atEnd next then
          return ⟨next, by omega⟩
        else
          throw "invalid token" ⟨pos, next⟩
  termination_by input.endPos.1 - pos.1
  decreasing_by
    all_goals (have := String.lt_sub_next h; omega)
  _ ← go {}
  match ← popBrace with
  | some (left, pos) => throwUnmatchedBrace left pos
  | none             => popIndent ⟨input.endPos, input.endPos⟩ 0

def run (input : String) (fileName : String) (fileMap : FileMap := input.toFileMap) : Except String (Array Token) :=
  let c : FileInfo := { content := input, fileMap, fileName }
  let s : State    := {}
  match (tokenize.run c).run s with
  | .ok _ s => .ok s.tokens
  | .error msg _ => .error msg
