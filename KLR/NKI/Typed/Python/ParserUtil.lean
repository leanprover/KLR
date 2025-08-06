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

import Lean
import Std.Data.HashSet

/-!
# Key changes:
- Differnet tokenizer:
  - Python strings with both `'` and `"` (TODO: Support python escape sequences)
  - Line comments, consumed as whitespace
  - Block comments with both `'''` and `"""`, parsed as a special token
  - No char literal
  - Python identifier: first char can be `_` or alpha, rest must be alphanum or `_`
-/

namespace Lean.Parser.SyntaxStack

def ofArray (a : Array Syntax) : SyntaxStack :=
  a.foldl SyntaxStack.push .empty

def toArray (s : SyntaxStack) : Array Syntax :=
  s.toSubarray.toArray

instance : Repr SyntaxStack where
  reprPrec s _ := "SyntaxStack.ofArray " ++ repr s.toArray

instance : Repr SyntaxStack where
  reprPrec a p := reprPrec (a.toSubarray) p

end Lean.Parser.SyntaxStack

-- namespace Lean.Parser.TokenTable

-- def addTokens (tt : TokenTable) (p : Parser) : TokenTable :=
--   let tkns := p.info.collectTokens []
--   tkns.foldl (λ tt t => tt.insert t t) tt

-- end Lean.Parser.TokenTable

namespace KLR.NKI.Typed.Python.Parser
open Lean
/-
# Import List
Only imports definitions that are not contaminated by Lean's built-in tokenizer behavior.
-/
open Parser (
  atomic
  andthenFn
  Parser
  ParserFn
  InputContext
  ParserModuleContext
  quotedStringFn -- TODO: make our own
  numberFnAux
  LeadingIdentBehavior
  ParserContext
  ParserState
  ParserInfo
  mkAtomicInfo
  PrattParsingTables
  longestMatchFn
  withAntiquotFn
  mkEmptySubstringAt
  takeWhileFn
  takeUntilFn
  Token
  mkAtom
  mkIdent
  FirstTokens
  TokenTable
  TokenMap
  pushNone
  checkNoImmediateColon

  manyNoAntiquot

  withAntiquotSpliceAndSuffix

  sepByNoAntiquot
  sepBy1NoAntiquot
  optionalNoAntiquot

  leadingNode
  withFn
  termParser -- sussy
  decQuotDepth
  checkNoWsBefore
  node
)

/-
# Export List
We carefully control what is exported from this file to control the tokenizer behavior.
The code in `Python/Parser.lean` must only use parser utilities exported here.

Note: The antiquot functions may call the built-in tokenizer. But this is fine since
it is only used in pattern matching.
-/
export Lean.Parser (
  maxPrec
  minPrec
  Parser
  ParserFn
  PrattParsingTables
  TokenTable
  Token

  eoi
  adaptCacheableContextFn
  withCacheFn
  mkAntiquot
  withAntiquot
  setExpected
)

/-
# ---------------------------Start of Custom Tokenizer--------------------------

Only functions marked with [CUSTOM] are actually different.
Otherwise, they are just copied over from Lean.Parser
-/

/--
[CUSTOM]

Consume whitespace and line comments
-/
partial def whitespace : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s
  else
    let curr := input.get' i h
    if curr == '\t' then
      s.mkUnexpectedError (pushMissing := false) "tabs are not allowed; please configure your editor to expand them"
    else if curr == '\r' then
      s.mkUnexpectedError (pushMissing := false) "isolated carriage returns are not allowed"
    else if curr.isWhitespace then whitespace c (s.next' input i h)
    -- line comments are ignored as whitespace
    else if curr == '#' then whitespace c (takeUntilFn (· == '\n') c s)
    else s

def ws : Parser :=
  { fn := whitespace }

private def isToken (idStartPos idStopPos : String.Pos) (tk : Option Token) : Bool :=
  match tk with
  | none    => false
  | some tk =>
     -- if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
    tk.endPos ≥ idStopPos - idStartPos

/-- Push `(Syntax.node tk <new-atom>)` onto syntax stack if parse was successful. -/
def mkNodeToken (n : SyntaxNodeKind) (startPos : String.Pos) : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let input     := c.input
  let stopPos   := s.pos
  let leading   := mkEmptySubstringAt input startPos
  let val       := input.extract startPos stopPos
  let s         := whitespace c s
  let wsStopPos := s.pos
  let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit n val info)

def mkTokenAndFixPos (startPos : String.Pos) (tk : Option Token) : ParserFn := fun c s =>
  match tk with
  | none    => s.mkErrorAt "token" startPos
  | some tk =>
    if c.forbiddenTk? == some tk then
      s.mkErrorAt "forbidden token" startPos
    else
      let input     := c.input
      let leading   := mkEmptySubstringAt input startPos
      let stopPos   := startPos + tk
      let s         := s.setPos stopPos
      let s         := whitespace c s
      let wsStopPos := s.pos
      let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
      let atom      := mkAtom (SourceInfo.original leading startPos trailing stopPos) tk
      s.pushSyntax atom

def mkIdResult (startPos : String.Pos) (tk : Option Token) (val : Name) : ParserFn := fun c s =>
  let stopPos           := s.pos
  if isToken startPos stopPos tk then
    mkTokenAndFixPos startPos tk c s
  else
    let input           := c.input
    let rawVal          := { str := input, startPos := startPos, stopPos := stopPos  : Substring }
    let s               := whitespace c s
    let trailingStopPos := s.pos
    let leading         := mkEmptySubstringAt input startPos
    let trailing        := { str := input, startPos := stopPos, stopPos := trailingStopPos : Substring }
    let info            := SourceInfo.original leading startPos trailing stopPos
    let atom            := mkIdent info rawVal val
    s.pushSyntax atom

/-- [CUSTOM] -/
@[inline] def isIdFirst (c : Char) : Bool :=
  c.isAlpha || c = '_'

/-- [CUSTOM] -/
@[inline] def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c = '_'

/-- [CUSTOM] -/
def identFnAux (startPos : String.Pos) (tk : Option Token) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then
    s.mkEOIError
  else
    let curr := input.get' i h
    if isIdFirst curr then
      let startPart := i
      let s         := takeWhileFn isIdRest c (s.next' input i h)
      let stopPart  := s.pos
      if isToken startPos s.pos tk then
        mkTokenAndFixPos startPos tk c s
      else
        let val := input.extract startPart stopPart
        mkIdResult startPos tk (.str .anonymous val) c s
    else
      mkTokenAndFixPos startPos tk c s

/--
[CUSTOM]

TODO: This does not properly implement Python's string escape sequence:
https://docs.python.org/3/reference/lexical_analysis.html#escape-sequences

We also don't support raw strings with the 'r' or 'R' prefix.
-/
partial def strLitFnAux (startPos : String.Pos) (quote : Char) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkUnexpectedErrorAt "unterminated string literal" startPos
  else
    let curr := input.get' i h
    let s    := s.setPos (input.next' i h)
    if curr == quote then
      mkNodeToken strLitKind startPos c s
    else if curr == '\\' then andthenFn quotedStringFn (strLitFnAux startPos quote) c s
    else strLitFnAux startPos quote c s

/-- [CUSTOM] -/
abbrev blockCommentKind : SyntaxNodeKind := `blockComment

/--
[CUSTOM]

Finish parsing a block comment started with `"""` or `'''`.

Note that block comments are parsed similar to statements in python,
where the start of a block comment must be properly indented according to the
current expected indentation level.
-/
partial def finishCommentBlock (startPos : String.Pos) (quote : Char) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then
    eoi s
  else
    let curr := input.get' i h
    if curr == '\\' then -- escape sequence
      let i := input.next' i h
      if h : input.atEnd i then eoi s else
      finishCommentBlock startPos quote c (s.next' input i h)
    else
      let j := input.nextWhile (· == quote) i
      if j == i then -- no quotation detected, continue comment
        finishCommentBlock startPos quote c (s.next' input i h)
      else
        let quote3 := ("".pushn quote 3).endPos
        if j - i ≥ quote3 then -- end of comment
          -- note that we only advance by 3 quotes, since there
          -- might be more quotes denoting the start of another comment
          mkNodeToken blockCommentKind startPos c (s.setPos (i + quote3))
        else -- not enough quotes, continue comment
          finishCommentBlock startPos quote c (s.setPos j)
where
  eoi s := s.mkUnexpectedError "unterminated comment"

/-- [CUSTOM] -/
private def tokenFnAux : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == '\"' then
    strOrCommentBlock curr c s
  else if curr == '\'' then
    strOrCommentBlock curr c s
  else if curr.isDigit then
    numberFnAux c s
  else
    let tk := c.tokens.matchPrefix input i
    identFnAux i tk c s
where
  strOrCommentBlock quote c s :=
    let input  := c.input
    let i      := s.pos
    let quote3 := "".pushn quote 3
    let j      := input.nextWhile (· == quote) i
    if j - i ≥ quote3.endPos then
      finishCommentBlock i quote c (s.setPos (i + quote3))
    else
      strLitFnAux i quote c (s.next input i)

private def updateTokenCache (startPos : String.Pos) (s : ParserState) : ParserState :=
  -- do not cache token parsing errors, which are rare and usually fatal and thus not worth an extra field in `TokenCache`
  match s with
  | ⟨stack, lhsPrec, pos, ⟨_, catCache⟩, none, errs⟩ =>
    if stack.size == 0 then s
    else
      let tk := stack.back
      ⟨stack, lhsPrec, pos, ⟨{ startPos := startPos, stopPos := pos, token := tk }, catCache⟩, none, errs⟩
  | other => other

def tokenFn (expected : List String := []) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then
    s.mkEOIError expected
  else
    let tkc := s.cache.tokenCache
    if tkc.startPos == i then
      let s := s.pushSyntax tkc.token
      s.setPos tkc.stopPos
    else
      let s := tokenFnAux c s
      updateTokenCache i s

/--
  Parses a token and asserts the result is of the given kind.
  `desc` is used in error messages as the token kind. -/
def expectTokenFn (k : SyntaxNodeKind) (desc : String) : ParserFn := fun c s =>
  let s := tokenFn [desc] c s
  if !s.hasError && !(s.stxStack.back.isOfKind k) then s.mkUnexpectedTokenError desc else s

/-- [CUSTOM] -/
def blockComment : Parser := {
  fn   := expectTokenFn blockCommentKind "block comment"
  info := mkAtomicInfo "blockComment"
}

/--
[CUSTOM]

`Lean.TSyntax.getString` is quite complicated and onlys works with Lean's
string lexical grammar. This implementation performs zero checks on the validity
of the string.
-/
def getString (s : StrLit) : String :=
  match Syntax.isLit? strLitKind s.raw with
  | some val => val.extract (val.next 0) (val.prev val.endPos)
  | _        => ""

/-
# ----------------------------End of Custom Tokenizer---------------------------
-/

def peekTokenAux (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn [] c s
  if let some _ := s.errorMsg then (s.restore iniSz iniPos, .error s)
  else
    let stx := s.stxStack.back
    (s.restore iniSz iniPos, .ok stx)

def peekToken (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let tkc := s.cache.tokenCache
  if tkc.startPos == s.pos then
    (s, .ok tkc.token)
  else
    peekTokenAux c s

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) (behavior : LeadingIdentBehavior) : ParserState × List α :=
  let (s, stx) := peekToken c s
  let find (n : Name) : ParserState × List α :=
    match map.find? n with
    | some as => (s, as)
    | _       => (s, [])
  match stx with
  | .ok (.atom _ sym)      => find (.mkSimple sym)
  | .ok (.ident _ _ val _) =>
    match behavior with
    | .default => find identKind
    | .symbol =>
      match map.find? val with
      | some as => (s, as)
      | none    => find identKind
    | .both =>
      match map.find? val with
      | some as =>
        if val == identKind then
          (s, as)  -- avoid running the same parsers twice
        else
          match map.find? identKind with
          | some as' => (s, as ++ as')
          | _        => (s, as)
      | none    => find identKind
  | .ok (.node _ k _) => find k
  | .ok _             => (s, [])
  | .error s'         => (s', [])

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
  if s.stackSize == iniSz + 1 then s
  else s.mkNode nullKind iniSz -- throw error instead?

def leadingParserAux (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) : ParserFn := fun c s => Id.run do
  let iniSz   := s.stackSize
  let (s, ps) := indexed tables.leadingTable c s behavior
  if s.hasError then
    return s
  let ps      := tables.leadingParsers ++ ps
  if ps.isEmpty then
    -- if there are no applicable parsers, consume the leading token and flag it as unexpected at this position
    let s := tokenFn [toString kind] c s
    if s.hasError then
      return s
    return s.mkUnexpectedTokenError (toString kind)
  let s := longestMatchFn none ps c s
  mkResult s iniSz

def leadingParser (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) (antiquotParser : ParserFn) : ParserFn :=
  withAntiquotFn (isCatAntiquot := true) antiquotParser (leadingParserAux kind tables behavior)

def trailingLoopStep (tables : PrattParsingTables) (left : Syntax) (ps : List (Parser × Nat)) : ParserFn := fun c s =>
  longestMatchFn left (ps ++ tables.trailingParsers) c s

partial def trailingLoop (tables : PrattParsingTables) (c : ParserContext) (s : ParserState) : ParserState := Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let (s, ps)       := indexed tables.trailingTable c s LeadingIdentBehavior.default
  if s.hasError then
    -- Discard token parse errors and break the trailing loop instead.
    -- The error will be flagged when the next leading position is parsed, unless the token
    -- is in fact valid there (e.g. EOI at command level, no-longer forbidden token)
    return s.restore iniSz iniPos
  if ps.isEmpty && tables.trailingParsers.isEmpty then
    return s -- no available trailing parser
  let left   := s.stxStack.back
  let s      := s.popSyntax
  let s      := trailingLoopStep tables left ps c s
  if s.hasError then
    -- Discard non-consuming parse errors and break the trailing loop instead, restoring `left`.
    -- This is necessary for fallback parsers like `app` that pretend to be always applicable.
    return if s.pos == iniPos then s.restore (iniSz - 1) iniPos |>.pushSyntax left else s
  trailingLoop tables c s

def prattParser (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) (antiquotParser : ParserFn) : ParserFn := fun c s =>
  let s := leadingParser kind tables behavior antiquotParser c s
  if s.hasError then
    s
  else
    trailingLoop tables c s

def numLitFn : ParserFn := expectTokenFn numLitKind "numeral"

def numLitNoAntiquot : Parser := {
  fn   := numLitFn
  info := mkAtomicInfo "num"
}

/-- The parser `num` parses a numeric literal in several bases:

* Decimal: `129`
* Hexadecimal: `0xdeadbeef`
* Octal: `0o755`
* Binary: `0b1101`

This parser has arity 1: it produces a `numLitKind` node containing an atom with the text of the
literal.
You can use `TSyntax.getNat` to extract the number from the resulting syntax object. -/
def numLit : Parser :=
  withAntiquot (mkAntiquot "num" numLitKind) numLitNoAntiquot

def scientificLitFn : ParserFn := expectTokenFn scientificLitKind "scientific number"

def scientificLitNoAntiquot : Parser := {
  fn   := scientificLitFn
  info := mkAtomicInfo "scientific"
}

/-- The parser `scientific` parses a scientific-notation literal, such as `1.3e-24`.

This parser has arity 1: it produces a `scientificLitKind` node containing an atom with the text
of the literal.
You can use `TSyntax.getScientific` to extract the parts from the resulting syntax object. -/
def scientificLit : Parser :=
  withAntiquot (mkAntiquot "scientific" scientificLitKind) scientificLitNoAntiquot

def strLitFn : ParserFn := expectTokenFn strLitKind "string literal"

def strLitNoAntiquot : Parser := {
  fn   := strLitFn
  info := mkAtomicInfo "str"
}

/-- The parser `str` parses a string literal, such as `"foo"` or `"\r\n"`. Strings can contain
C-style escapes like `\n`, `\"`, `\x00` or `\u2665`, as well as literal unicode characters like `∈`.
Newlines in a string are interpreted literally.

This parser has arity 1: it produces a `strLitKind` node containing an atom with the raw
literal (including the quote marks and without interpreting the escapes).
You can use `TSyntax.getString` to decode the string from the resulting syntax object. -/
def strLit : Parser :=
  withAntiquot (mkAntiquot "str" strLitKind) strLitNoAntiquot

def identFn : ParserFn := expectTokenFn identKind "identifier"

def identNoAntiquot : Parser := {
  fn   := identFn
  info := mkAtomicInfo "ident"
}

/-- The parser `ident` parses a single identifier, possibly with namespaces, such as `foo` or
`bar.baz`. The identifier must not be a declared token, so for example it will not match `"def"`
because `def` is a keyword token. Tokens are implicitly declared by using them in string literals
in parser declarations, so `syntax foo := "bla"` will make `bla` no longer legal as an identifier.

Identifiers can contain special characters or keywords if they are escaped using the `«»` characters:
`«def»` is an identifier named `def`, and `«x»` is treated the same as `x`. This is useful for
using disallowed characters in identifiers such as `«foo.bar».baz` or `«hello world»`.

This parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.
You can use `TSyntax.getId` to extract the name from the resulting syntax object. -/
def ident : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) identNoAntiquot

def satisfySymbolFn (p : String → Bool) (expected : List String) : ParserFn := fun c s => Id.run do
  let iniPos := s.pos
  let s := tokenFn expected c s
  if s.hasError then
    return s
  if let .atom _ sym := s.stxStack.back then
    if p sym then
      return s
  -- this is a very hot `mkUnexpectedTokenErrors` call, so explicitly pass `iniPos`
  s.mkUnexpectedTokenErrors expected iniPos

def symbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
  satisfySymbolFn (fun s => s == sym) [errorMsg]

def symbolInfo (sym : String) : ParserInfo := {
  collectTokens := fun tks => sym :: tks
  firstTokens   := FirstTokens.tokens [ sym ]
}

def symbolFn (sym : String) : ParserFn :=
  symbolFnAux sym ("'" ++ sym ++ "'")

def symbolNoAntiquot (sym : String) : Parser :=
  let sym := sym.trim
  { info := symbolInfo sym
    fn   := symbolFn sym }

-- We support three kinds of antiquotations: `$id`, `$_`, and `$(t)`, where `id` is a term identifier and `t` is a term.
def antiquotNestedExpr : Parser := node `antiquotNestedExpr (symbolNoAntiquot "(" >> decQuotDepth termParser >> symbolNoAntiquot ")")
def antiquotExpr : Parser       := identNoAntiquot <|> symbolNoAntiquot "_" <|> antiquotNestedExpr

def tokenAntiquotFn : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := (checkNoWsBefore >> symbolNoAntiquot "%" >> symbolNoAntiquot "$" >> checkNoWsBefore >> antiquotExpr).fn c s
  if s.hasError then
    return s.restore iniSz iniPos
  s.mkNode (`token_antiquot) (iniSz - 1)

def tokenWithAntiquot : Parser → Parser := withFn fun f c s =>
  let s := f c s
  -- fast check that is false in most cases
  if c.input.get s.pos == '%' then
    tokenAntiquotFn c s
  else
    s

def symbol (sym : String) : Parser :=
  tokenWithAntiquot (symbolNoAntiquot sym)

instance : Coe String Parser where
  coe := symbol

/-
`sepByNoAntiquot` and `sepBy1NoAntiquot` is safe.
But `sepByElemParser` calls `symbol`.
Same story with `optional`.
-/

def sepByElemParser (p : Parser) (sep : String) : Parser :=
  withAntiquotSpliceAndSuffix `sepBy p (symbol (sep.trim ++ "*"))

def sepBy (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  sepByNoAntiquot (sepByElemParser p sep) psep allowTrailingSep

def sepBy1 (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  sepBy1NoAntiquot (sepByElemParser p sep) psep allowTrailingSep

/-- The parser `optional(p)`, or `(p)?`, parses `p` if it succeeds,
otherwise it succeeds with no value.

Note that because `?` is a legal identifier character, one must write `(p)?` or `p ?` for
it to parse correctly. `ident?` will not work; one must write `(ident)?` instead.

This parser has arity 1: it produces a `nullKind` node containing either zero arguments
(for the `none` case) or the list of arguments produced by `p`.
(In particular, if `p` has arity 0 then the two cases are not differentiated!) -/
def optional (p : Parser) : Parser :=
  optionalNoAntiquot (withAntiquotSpliceAndSuffix `optional p (symbol "?"))

/-
# New
-/

def runParser (source fileName : String) (p : Parser) (tokens : TokenTable) : IO ParserState := do
  let emptyEnv ← mkEmptyEnvironment 0
  let ictx : InputContext := {
    input    := source,
    fileName := fileName
    fileMap  := FileMap.ofString source
  }

  let pmctx : ParserModuleContext := { env := emptyEnv, options := {} }
  let s : ParserState := {
    pos      := 0
    cache    := {
      tokenCache  := { startPos := source.endPos + ' ' }
      parserCache := {}
    }
  }
  let s := p.fn.run ictx pmctx tokens s
  pure s


/-
# -------------------Set Builder Notation for TokenTable/Map--------------------
-/

instance : Insert (Name × Parser × Nat) (TokenMap (Parser × Nat)) where
  insert | (n, p, prec), tm => tm.insert n (p, prec)

instance : Singleton (Name × Parser × Nat) (TokenMap (Parser × Nat)) where
  singleton | (n, p, prec) => TokenMap.insert {} n (p, prec)

instance : Insert Token TokenTable := ⟨fun a b => b.insert a a⟩

instance : Singleton Token TokenTable := ⟨fun a => insert a ∅⟩

instance : HAppend TokenTable (List Token) TokenTable where
  hAppend tt tl :=
    tl.foldl (fun tt t => tt.insert t t) tt

def TokenTable.empty : TokenTable := .empty
