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

import Aesop
import KLR.NKI.Typed.Python.Basic
import KLR.NKI.Typed.Python.PosLemmas
import KLR.NKI.Typed.Python.Util


namespace KLR.NKI.Typed.Python.Tokenizer

/-
https://docs.python.org/3/reference/lexical_analysis.html

TODO: softline break inside braces/parens/brackets
-/

open Lean (FileMap)

inductive TokenKind
  -- Literals
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | ident (name : Ident)

  -- Keywords
  -- https://docs.python.org/3/reference/lexical_analysis.html#keywords
  | False | await | else | import | pass
  | None | break | except | in | raise
  | True | class | finally | is | return
  | and | continue | for | lambda | try
  | as | def | from | nonlocal | while
  | assert | del | global | not | with
  | async | elif | if | or | yield

  -- Operators
  -- https://docs.python.org/3/reference/lexical_analysis.html#operators
  | plus | minus | star | dstar | slash | dslash | percent | at /- @ is also a delimiter -/
  | lshift | rshift | amp | pipe | caret | tilde | colonassign
  | lt | gt | le | ge | eq | ne

  -- Delimiters
  -- https://docs.python.org/3/reference/lexical_analysis.html#delimiters
  | lparen | rparen | lbracket | rbracket | lbrace | rbrace
  | comma | colon | bang | dot | semicolon | assign
  | rarrow | plusassign | minusassign | starassign | slashassign | dslashassign | percentassign
  | atassign | ampassign | pipeassign | caretassign | rshiftassign | lshiftassign | dstarassign
  | ellipsis

  -- Special
  | newline | indent | dedent
deriving BEq, Repr, Inhabited

def TokenKind.toString : TokenKind → String
  | .int    value  => s!"{value}"
  | .float  value  => s!"{value}"
  | .string value  => s!"`{value}`"
  | .ident  name   => name
  | .False         => "False"
  | .await         => "await"
  | .else          => "else"
  | .import        => "import"
  | .pass          => "pass"
  | .None          => "None"
  | .break         => "break"
  | .except        => "except"
  | .in            => "in"
  | .raise         => "raise"
  | .True          => "True"
  | .class         => "class"
  | .finally       => "finally"
  | .is            => "is"
  | .return        => "return"
  | .and           => "and"
  | .continue      => "continue"
  | .for           => "for"
  | .lambda        => "lambda"
  | .try           => "try"
  | .as            => "as"
  | .def           => "def"
  | .from          => "from"
  | .nonlocal      => "nonlocal"
  | .while         => "while"
  | .assert        => "assert"
  | .del           => "del"
  | .global        => "global"
  | .not           => "not"
  | .with          => "with"
  | .async         => "async"
  | .elif          => "elif"
  | .if            => "if"
  | .or            => "or"
  | .yield         => "yield"
  | .plus          => "+"
  | .minus         => "-"
  | .star          => "*"
  | .dstar         => "**"
  | .slash         => "/"
  | .dslash        => "//"
  | .percent       => "%"
  | .at            => "@"
  | .lshift        => "<<"
  | .rshift        => ">>"
  | .amp           => "&"
  | .pipe          => "|"
  | .caret         => "^"
  | .tilde         => "~"
  | .colonassign   => ":="
  | .lt            => "<"
  | .gt            => ">"
  | .le            => "<="
  | .ge            => ">="
  | .eq            => "=="
  | .ne            => "!="
  | .lparen        => "("
  | .rparen        => ")"
  | .lbracket      => "["
  | .rbracket      => "]"
  | .lbrace        => "{"
  | .rbrace        => "}"
  | .comma         => ","
  | .colon         => ":"
  | .bang          => "!"
  | .dot           => "."
  | .semicolon     => ";"
  | .assign        => "="
  | .rarrow        => "->"
  | .plusassign    => "+="
  | .minusassign   => "-="
  | .starassign    => "*="
  | .slashassign   => "/="
  | .dslashassign  => "//="
  | .percentassign => "%="
  | .atassign      => "@="
  | .ampassign     => "&="
  | .pipeassign    => "|="
  | .caretassign   => "^="
  | .rshiftassign  => ">>="
  | .lshiftassign  => "<<="
  | .dstarassign   => "**="
  | .ellipsis      => "..."
  | .newline       => "NEWLINE"
  | .indent        => "INDENT"
  | .dedent        => "DEDENT"

instance instToStingTokenKind : ToString TokenKind := ⟨TokenKind.toString⟩

structure Token where
  kind   : TokenKind
  pos    : String.Pos
  endPos : String.Pos
deriving Repr, Inhabited, BEq

structure Context where
  input    : String
  fileName : String
  fileMap  : FileMap

structure State where
  tokens      : Array Token    := #[]
  indentStack : List Nat       := [0]
  /-- https://docs.python.org/3/reference/lexical_analysis.html#implicit-line-joining -/
  lineJoin    : Bool           := false
  bracesStack : List TokenKind := []

abbrev TokenizerM := ReaderT Context (EStateM String State)

inductive TkResult (startPos : String.Pos)
  | success (rest : PosGt startPos)
  | failure

def TkResult.isSuccess {startPos : String.Pos} : TkResult startPos → Bool
  | .success _ => true
  | .failure   => false

instance : HasFileInfo TokenizerM where
  fileName := return (← read).fileName
  fileMap := return (← read).fileMap

/--
TODO: Python-style errors where we print out the relevant source code.
-/
def throw {α} (msg : String) (startPos endPos : String.Pos) : TokenizerM α := do
  let msg ← formatError "SyntaxError" msg startPos endPos
  monadLift (m := EStateM String State) (EStateM.throw msg)

def throwInternal {α} (startPos endPos : String.Pos) : TokenizerM α := do
  throw "unexpected internal error, please report!" startPos endPos

def indentLevel (startPos endPos : String.Pos) : TokenizerM Nat := do
  let { indentStack, .. } ← get
  match indentStack.head? with
  | some n => pure n
  | none   => throwInternal startPos endPos

def getInput : TokenizerM String :=
  return (← read).input

def pushToken (tk : TokenKind) (startPos endPos : String.Pos) : TokenizerM Unit := do
  let s ← get
  set {s with tokens := s.tokens.push ⟨tk, startPos, endPos⟩}

def getLineJoin : TokenizerM Bool := do
  pure (← get).lineJoin

def setLineJoin (lj : Bool) : TokenizerM Unit := do
  let s ← get
  set {s with lineJoin := lj}

def getBracesStack : TokenizerM (List TokenKind) := do
  pure (← get).bracesStack

def pushBrace (br : TokenKind) : TokenizerM Unit := do
  let s ← get
  set {s with bracesStack := br :: s.bracesStack}

def popBrace : TokenizerM (Option TokenKind) := do
  let s ← get
  let stack := s.bracesStack
  set {s with bracesStack := stack.tail}
  pure stack.head?

def bracesStackempty : TokenizerM Bool := do
  pure (← get).bracesStack.isEmpty

def isPythonWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == Char.ofNat 0x0C /- form feed -/

def newline (startPos : String.Pos) : TokenizerM (TkResult startPos) := do
  let input ← getInput
  let input := input.extract startPos input.endPos
  let endPos : Option (PosGt startPos) :=
         if input.startsWith "\r\n" then some ⟨startPos + "\r\n", String.add_gt startPos _ (by simp_str_size)⟩
    else if input.startsWith "\r"   then some ⟨startPos + "\r"  , String.add_gt startPos _ (by simp_str_size)⟩
    else if input.startsWith "\n"   then some ⟨startPos + "\n"  , String.add_gt startPos _ (by simp_str_size)⟩
    else none
  match endPos with
  | some endPos => pure <| .success endPos
  | none        => pure .failure

def pushIndent (startPos endPos : String.Pos) (n : Nat) : TokenizerM Unit := do
  let s ← get
  set {s with indentStack := n :: s.indentStack}
  pushToken .indent startPos endPos

def popIndent (startPos endPos : String.Pos) (n : Nat) : TokenizerM Unit := do
  let stack := (← get).indentStack
  let newStack ← go stack
  modifyGet fun s =>
  ((), {s with indentStack := newStack})
where
  go : List Nat → TokenizerM (List Nat)
  | [] => throwInternal startPos endPos
  | hd :: tl => do
    if hd == n then
      pure (hd :: tl)
    else if hd > n then
      pushToken .dedent startPos endPos
      go tl
    else
      throw "inconsistent dedent" startPos endPos

def finishLineComment (startPos : String.Pos) : TokenizerM (PosGe startPos) := do
  let input ← getInput
  let rec skip (pos : String.Pos) : PosGe pos :=
    if h : input.atEnd pos then ⟨pos, by simp⟩ else
    let curr := input.get' pos h
    let next := input.next' pos h
    if curr == '\n' then
      ⟨pos, by simp⟩
    else
      have := input.lt_sub_next _ h
      let pos := skip next
      ⟨pos.val, pos.next_ge⟩
  termination_by (input.endPos - pos).byteIdx
  pure <| skip startPos

def checkIndent (startPos : String.Pos) : TokenizerM (PosGt startPos ⊕ PosGe startPos) := do
  let input ← getInput
  let rec countIndent (n : Nat) (pos : String.Pos) : TokenizerM (Nat × PosGe pos) := do
    if h : input.atEnd pos then return (n, ⟨pos, by simp_pos⟩) else
    match input.get' pos h with
    | '\t' =>
      throw "tabs not supported, please configure your editor to use spaces" startPos pos
    | ' ' =>
      have := input.lt_sub_next _ h
      let (n', pos') ← countIndent (n + 1) (input.next' pos h)
      pure (n', ⟨pos', pos'.next_ge⟩)
    | _ => pure (n, ⟨pos, by simp_pos⟩)
  termination_by (input.endPos - pos).byteIdx

  let (currIndent, endPos) ← countIndent 0 startPos

  -- We should technically do `.inl` here, but we may be advance the pointer
  if h : input.atEnd endPos then pure <| .inr endPos else

  if input.get' endPos h == '#' then
    let next := input.next' endPos h
    let endPos ← finishLineComment next
    let ⟨endPos, h⟩ : PosGt startPos := ⟨endPos.val, by
      rename_i endPos'
      obtain ⟨endPos', h'⟩ := endPos'
      obtain ⟨endPos, he⟩ := endPos
      have := String.lt_next' input endPos'
      rw [← String.next'_eq _ _ h] at this
      have := String.lt_next' input endPos'
      simp only [String.next'_eq, ge_iff_le, next] at he
      simp_all only [String.next'_eq, String.pos_lt_eq, gt_iff_lt, next]
      omega
    ⟩
    match ← newline endPos with
    | .success ⟨res, h'⟩ => pure <| .inl ⟨res, by omega⟩
    | .failure => pure <| .inl ⟨endPos, h⟩
  else
    match ← newline endPos with
    | .success endPos => pure <| .inl ⟨endPos.val, endPos.gt_of_trans_gt⟩
    | .failure =>
      let indent ← indentLevel startPos endPos
      if currIndent > indent then
        pushIndent startPos endPos currIndent
      else if currIndent < indent then
        popIndent startPos endPos currIndent
      pure <| .inr endPos

@[inline] def throwUnmatchedBrace {α} (brace : TokenKind) (startPos endPos : String.Pos) : TokenizerM α := do
  throw s!"unmatched {brace}" startPos endPos

@[inline] def bracesMatch : TokenKind → TokenKind → Bool
  | .lparen  , .rparen
  | .lbrace  , .rbrace
  | .lbracket, .rbracket => true
  | _        , _         => false

def checkBraces (brace : TokenKind) (startPos endPos : String.Pos) : TokenizerM Unit := do
  match brace with
  | .lparen | .lbrace | .lbracket =>
    pushBrace brace; setLineJoin true
  | .rparen | .rbrace | .rbracket =>
    match ← popBrace with
    | some left =>
      if bracesMatch left brace then
        if ← bracesStackempty then setLineJoin false
      else
        throwUnmatchedBrace left startPos endPos
    | none =>
      throwUnmatchedBrace brace startPos endPos
  | _ => return

def operatorAndDelimiter (startPos : String.Pos) : TokenizerM (TkResult startPos) := do
  let input ← getInput
  let subStr := input.extract startPos (startPos + ⟨3⟩)
  let res : Option (TokenKind × PosGt startPos) :=
         if subStr.startsWith "..." then some (.ellipsis,      ⟨startPos + "...", String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "<<=" then some (.lshiftassign,  ⟨startPos + "<<=", String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ">>=" then some (.rshiftassign,  ⟨startPos + ">>=", String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "**=" then some (.dstarassign,   ⟨startPos + "**=", String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "//=" then some (.dslashassign,  ⟨startPos + "//=", String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "->"  then some (.rarrow,        ⟨startPos + "->" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "*="  then some (.starassign,    ⟨startPos + "*=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "/="  then some (.slashassign,   ⟨startPos + "/=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "%="  then some (.percentassign, ⟨startPos + "%=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "+="  then some (.plusassign,    ⟨startPos + "+=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "-="  then some (.minusassign,   ⟨startPos + "-=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "@="  then some (.atassign,      ⟨startPos + "@=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "&="  then some (.ampassign,     ⟨startPos + "&=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "|="  then some (.pipeassign,    ⟨startPos + "|=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "^="  then some (.caretassign,   ⟨startPos + "^=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ":="  then some (.colonassign,   ⟨startPos + ":=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "<<"  then some (.lshift,        ⟨startPos + "<<" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ">>"  then some (.rshift,        ⟨startPos + ">>" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "**"  then some (.dstar,         ⟨startPos + "**" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "//"  then some (.dslash,        ⟨startPos + "//" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "=="  then some (.eq,            ⟨startPos + "==" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "!="  then some (.ne,            ⟨startPos + "!=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "<="  then some (.le,            ⟨startPos + "<=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ">="  then some (.ge,            ⟨startPos + ">=" , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "<"   then some (.lt,            ⟨startPos + "<"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ">"   then some (.gt,            ⟨startPos + ">"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "+"   then some (.plus,          ⟨startPos + "+"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "-"   then some (.minus,         ⟨startPos + "-"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "*"   then some (.star,          ⟨startPos + "*"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "/"   then some (.slash,         ⟨startPos + "/"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "%"   then some (.percent,       ⟨startPos + "%"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "&"   then some (.amp,           ⟨startPos + "&"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "|"   then some (.pipe,          ⟨startPos + "|"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "^"   then some (.caret,         ⟨startPos + "^"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "~"   then some (.tilde,         ⟨startPos + "~"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "("   then some (.lparen,        ⟨startPos + "("  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ")"   then some (.rparen,        ⟨startPos + ")"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "["   then some (.lbracket,      ⟨startPos + "["  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "]"   then some (.rbracket,      ⟨startPos + "]"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "{"   then some (.lbrace,        ⟨startPos + "{"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "}"   then some (.rbrace,        ⟨startPos + "}"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ","   then some (.comma,         ⟨startPos + ","  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ":"   then some (.colon,         ⟨startPos + ":"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "@"   then some (.at,            ⟨startPos + "@"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "!"   then some (.bang,          ⟨startPos + "!"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "."   then some (.dot,           ⟨startPos + "."  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith ";"   then some (.semicolon,     ⟨startPos + ";"  , String.add_gt startPos _ (by simp_str_size)⟩)
    else if subStr.startsWith "="   then some (.assign,        ⟨startPos + "="  , String.add_gt startPos _ (by simp_str_size)⟩)
    else none
  match res with
  | some (tk, endPos) =>
    checkBraces tk startPos endPos
    pushToken tk startPos endPos
    pure <| .success endPos
  | none => pure .failure

def decodeStrEscape (startPos : String.Pos) (s : String) : TokenizerM (String × PosGe startPos) := do
  let input ← getInput
  match ← newline startPos with
  | .success ⟨pos, h⟩ =>
    pure (s, ⟨pos, by omega⟩)
  | .failure => -- escape sequence
    if h : input.atEnd startPos then throw "unterminated string literal" startPos startPos else
    let curr := input.get' startPos h
    let endPos := PosGe.next' startPos h
    -- TODO: This behavior is different from the Python spec
    match curr with
    | '\\'
    | '\"'
    | '\'' => pure (s.push curr        , endPos)
    | 'a'  => pure (s.push (.ofNat 0x7), endPos)
    | 'b'  => pure (s.push (.ofNat 0x8), endPos)
    | 'f'  => pure (s.push (.ofNat 0xc), endPos)
    | 'n'  => pure (s.push '\n'        , endPos)
    | 'r'  => pure (s.push '\r'        , endPos)
    | 't'  => pure (s.push '\t'        , endPos)
    | 'v'  => pure (s.push (.ofNat 0xb), endPos)
    | _    => throw "invalid escape sequence" startPos (input.next' startPos h)

def finishShortStr (startPos : String.Pos) (firstQuote : Char) : TokenizerM (String × PosGe startPos) := do
  let input ← getInput
  let rec go (s : String) (startPos : String.Pos) : TokenizerM (String × PosGe startPos) := do
    if h : input.atEnd startPos then throw "unterminated string literal" startPos startPos else
    if (← newline startPos).isSuccess then throw "unterminated string literal" startPos startPos else

    let curr := input.get' startPos h
    let next := input.next' startPos h

    if curr == firstQuote then
      pure (s, PosGe.next' startPos h)
    else if curr == '\\' then
      let (s, endPos) ← decodeStrEscape next s
      have := endPos.lt_sub_next
      let (s, endPos) ← go s endPos
      pure (s, ⟨endPos.val, PosGe.ge_of_next_of_ge_of_ge input startPos h _ endPos⟩)
    else
      have := input.lt_sub_next startPos h
      let (s, endPos) ← go (s.push curr) (PosGe.next' startPos h)
      pure (s, ⟨endPos.val, endPos.next_ge (h := h)⟩)
  termination_by (input.endPos - startPos).byteIdx
  go "" startPos

def finishLongStr (startPos : String.Pos) (firstQuote : Char) : TokenizerM (String × PosGe startPos) := do
  let input ← getInput
  let tquote := "".pushn firstQuote 3
  let rec go (s : String) (startPos : String.Pos) : TokenizerM (String × PosGe startPos) := do
    if h : input.atEnd startPos then throw "unterminated string literal" startPos startPos else

    if tquote == input.extract startPos (startPos + tquote) then pure (s, ⟨startPos + tquote, by simp⟩) else

    let curr := input.get' startPos h
    let next := input.next' startPos h

    if curr == '\\' then
      let (s, endPos) ← decodeStrEscape next s
      have := endPos.lt_sub_next
      let (s, endPos) ← go s endPos
      pure (s, ⟨endPos.val, PosGe.ge_of_next_of_ge_of_ge input startPos h _ endPos⟩)
    else
      have := input.lt_sub_next startPos h
      let (s, endPos) ← go (s.push curr) (PosGe.next' startPos h)
      pure (s, ⟨endPos.val, endPos.next_ge (h := h)⟩)
  termination_by (input.endPos - startPos).byteIdx
  go "" startPos

def finishStr (startPos : String.Pos) (firstQuote : Char) : TokenizerM (String × PosGe startPos) := do
  let input ← getInput
  let dquote := "".pushn firstQuote 2
  if (input.extract startPos input.endPos).startsWith dquote then
    let pos := startPos + dquote
    let (s, endPos) ← finishLongStr pos firstQuote
    pure (s, ⟨endPos.val, endPos.ge_of_ge <| dquote.add_ge startPos⟩)
  else
    finishShortStr startPos firstQuote

def isIdFirst (c : Char) : Bool :=
  c.isAlpha || c == '_'

def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c == '_'

def finishIdent (startPos : String.Pos) (first : Char) : TokenizerM (String × PosGe startPos) := do
  let input ← getInput
  let rec go (s : String) (pos : String.Pos) : String × PosGe pos :=
    if h : input.atEnd pos then (s, ⟨pos, by simp⟩) else
    let curr := input.get' pos h
    if isIdRest curr then
      let next := input.next' pos h
      have := input.lt_sub_next _ h
      let (s, pos) := go (s.push curr) next
      (s, ⟨pos.val, pos.next_ge⟩)
    else
      (s, ⟨pos, by simp⟩)
  termination_by (input.endPos - pos).byteIdx
  pure <| go first.toString startPos

def decodeNat (s : String) (startPos endPos : String.Pos) : TokenizerM Nat := do
  match s.toNat? with
  | some n => pure n
  | none   => throw "invalid int literal" startPos endPos

def decodeFloatAux (s : String) : Option Float := do
  let [before, after] := s.split (· == '.') | none
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

def decodeFloat (s : String) (startPos endPos : String.Pos) : TokenizerM Float := do
  match decodeFloatAux s with
  | some float => pure float
  | none       => throw "invalid float literal" startPos endPos

/--
TODO: Implement full pythonic numeric literal
-/
def finishNum (startPos : String.Pos) (first : Char) : TokenizerM (TokenKind × PosGe startPos) := do
  let input ← getInput
  let rec extractDigits (s : String) (startPos : String.Pos) : String × PosGe startPos :=
    if h : input.atEnd startPos then (s, ⟨startPos, by simp⟩) else
    let curr := input.get' startPos h
    if curr.isDigit then
      let next := input.next' startPos h
      have := input.lt_sub_next startPos h
      let (s, pos) := extractDigits (s.push curr) next
      (s, ⟨pos.val, pos.next_ge⟩)
    else
      (s, ⟨startPos, by simp⟩)
  termination_by (input.endPos - startPos).byteIdx

  let (int, pos) := extractDigits first.toString startPos
  if h : input.atEnd pos then pure (.int <| ← decodeNat int startPos pos, pos) else
  let curr := input.get' pos h
  let next := input.next' pos h
  if curr != '.' then pure (.int <| ← decodeNat int startPos pos, pos) else

  let (decimal, endPos) := extractDigits "" next
  let float ← decodeFloat (int ++ "." ++ decimal) startPos endPos
  pure (.float float, ⟨endPos.val, PosGe.ge_next_gt_trans_ge pos h endPos⟩)

/--
Ensure proper separation of a numeric literal with the next token.
-/
def checkNumLitEnd (startPos endPos : String.Pos) : TokenizerM Unit := do
  let input ← getInput
  if h : input.atEnd endPos then return else
  let curr := input.get' endPos h
  if isIdRest curr then
    throw "invalid numeric literal" startPos endPos

def identKind : String → TokenKind
  | "False"    => .False
  | "await"    => .await
  | "else"     => .else
  | "import"   => .import
  | "pass"     => .pass
  | "None"     => .None
  | "break"    => .break
  | "except"   => .except
  | "in"       => .in
  | "raise"    => .raise
  | "True"     => .True
  | "class"    => .class
  | "finally"  => .finally
  | "is"       => .is
  | "return"   => .return
  | "and"      => .and
  | "continue" => .continue
  | "for"      => .for
  | "lambda"   => .lambda
  | "try"      => .try
  | "as"       => .as
  | "def"      => .def
  | "from"     => .from
  | "nonlocal" => .nonlocal
  | "while"    => .while
  | "assert"   => .assert
  | "del"      => .del
  | "global"   => .global
  | "not"      => .not
  | "with"     => .with
  | "async"    => .async
  | "elif"     => .elif
  | "if"       => .if
  | "or"       => .or
  | "yield"    => .yield
  | id         => .ident id

def tokenizeLine (startPos : String.Pos) : TokenizerM (PosGe startPos) := do
  let input ← getInput
  let rec go (startPos : String.Pos) : TokenizerM (PosGe startPos) := do
    if h : input.atEnd startPos then return ⟨startPos, by simp⟩ else

    match ← newline startPos with
    | .success ⟨pos, h⟩ =>
      if !(← getLineJoin) then pushToken .newline startPos pos
      return ⟨pos, by omega⟩
    | .failure => pure

    let curr := input.get' startPos h
    let next := input.next' startPos h

    let cont (endPos : PosGe next) : TokenizerM (PosGe startPos) := do
      have := endPos.lt_sub_next
      let res ← go endPos
      pure ⟨res.val, endPos.next_ge_trans_ge res⟩

    if curr == '\\' then -- explicit line break
      let res ← newline next
      match res with
      | .success pos =>
        have := pos.lt_sub_next
        let endPos ← go pos
        pure ⟨endPos.val, endPos.next_gt_trans_ge⟩
      | .failure =>
        throw "unexpected character after line continuation character" startPos next
    else if curr == '#' then -- line comments
      cont <| ← finishLineComment next
    else if isPythonWhitespace curr then -- white space
      have := input.lt_sub_next startPos h
      let endPos ← go next
      pure ⟨endPos.val, endPos.next_ge⟩
    else if curr.isDigit then -- numeric literal
      let (tk, endPos) ← finishNum next curr
      checkNumLitEnd startPos endPos
      pushToken tk startPos endPos
      cont endPos
    else if curr == '\'' || curr == '\"' then
      let (str, endPos) ← finishStr next curr
      pushToken (.string str) startPos endPos
      cont endPos
    else if isIdFirst curr then
      let (id, endPos) ← finishIdent next curr
      pushToken (identKind id) startPos endPos
      cont endPos
    else
      match ← operatorAndDelimiter startPos with
      | .success pos =>
        have := pos.lt_start startPos input h
        let endPos ← go pos
        pure ⟨endPos.val, endPos.ge_of_trans_gt⟩
      | .failure =>
        throw "unexpected character" startPos next
  termination_by (input.endPos - startPos).byteIdx
  go startPos

def tokenize : TokenizerM Unit := do
  let input ← getInput
  let rec go (startPos : String.Pos) : TokenizerM (PosGe startPos) := do
    if h : input.atEnd startPos then pure ⟨startPos, by simp⟩ else
    match ← checkIndent startPos with
    | .inl pos =>
      have := pos.lt_start startPos input h
      let res ← go pos.val
      pure ⟨res.val, pos.ge_of_trans_gt res⟩
    | .inr pos =>
      let endPos ← tokenizeLine startPos
      if hgt : endPos.val.byteIdx > pos.val.byteIdx then
        have := endPos.lt_of_gt input startPos h
        let res ← go endPos.val
        pure ⟨res.val, endPos.ge_of_trans_ge res⟩
      else
        if input.atEnd endPos then
          pure endPos
        else
          throwInternal pos endPos
  termination_by (input.endPos - startPos).byteIdx
  _ ← go {}
  match ← popBrace with
  | some left => throwUnmatchedBrace left input.endPos input.endPos
  | none => popIndent input.endPos input.endPos 0

def run (input : String) (fileName : String) (fileMap : FileMap := input.toFileMap) : Except String (Array Token) :=
  let c : Context := { input, fileMap, fileName }
  let s : State   := {}
  match (tokenize.run c).run s with
  | .ok _ s => .ok s.tokens
  | .error msg _ => .error msg

namespace Test

  def tokensToString (tokens : Array Token) : String :=
    String.intercalate " " (tokens.map (TokenKind.toString ∘ Token.kind)).toList

  def test (s : String) : String :=
    let tokens := run s "<input>"
    match tokens with
    | .ok tokens => tokensToString tokens
    | .error msg => msg
