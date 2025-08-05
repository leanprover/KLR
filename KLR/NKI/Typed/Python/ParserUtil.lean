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
-/
export Lean.Parser (
  maxPrec
  minPrec
  Parser
  ParserFn
  PrattParsingTables
  TokenTable
  Token

  identNoAntiquot
  adaptCacheableContextFn
  withCacheFn
  mkAntiquot
  symbol
  withAntiquot
  setExpected
  numLit
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
    strOrCommentBlock '\"' c s
  else if curr == '\'' then
    strOrCommentBlock '\'' c s
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

-- def identFn : ParserFn := expectTokenFn identKind "identifier"

-- def identNoAntiquot : Parser := {
--   fn   := identFn
--   info := mkAtomicInfo "ident"
-- }

-- def satisfySymbolFn (p : String → Bool) (expected : List String) : ParserFn := fun c s => Id.run do
--   let iniPos := s.pos
--   let s := tokenFn expected c s
--   if s.hasError then
--     return s
--   if let .atom _ sym := s.stxStack.back then
--     if p sym then
--       return s
--   -- this is a very hot `mkUnexpectedTokenErrors` call, so explicitly pass `iniPos`
--   s.mkUnexpectedTokenErrors expected iniPos

-- def symbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
--   satisfySymbolFn (fun s => s == sym) [errorMsg]

-- def symbolInfo (sym : String) : ParserInfo := {
--   collectTokens := fun tks => sym :: tks
--   firstTokens   := FirstTokens.tokens [ sym ]
-- }

-- def symbolFn (sym : String) : ParserFn :=
--   symbolFnAux sym ("'" ++ sym ++ "'")

-- def symbolNoAntiquot (sym : String) : Parser :=
--   let sym := sym.trim
--   { info := symbolInfo sym
--     fn   := symbolFn sym }

-- -- We support three kinds of antiquotations: `$id`, `$_`, and `$(t)`, where `id` is a term identifier and `t` is a term.
-- def antiquotNestedExpr : Parser := node `antiquotNestedExpr (symbolNoAntiquot "(" >> decQuotDepth termParser >> symbolNoAntiquot ")")
-- def antiquotExpr : Parser       := identNoAntiquot <|> symbolNoAntiquot "_" <|> antiquotNestedExpr

-- def tokenAntiquotFn : ParserFn := fun c s => Id.run do
--   if s.hasError then
--     return s
--   let iniSz  := s.stackSize
--   let iniPos := s.pos
--   let s      := (checkNoWsBefore >> symbolNoAntiquot "%" >> symbolNoAntiquot "$" >> checkNoWsBefore >> antiquotExpr).fn c s
--   if s.hasError then
--     return s.restore iniSz iniPos
--   s.mkNode (`token_antiquot) (iniSz - 1)

-- def tokenWithAntiquot : Parser → Parser := withFn fun f c s =>
--   let s := f c s
--   -- fast check that is false in most cases
--   if c.input.get s.pos == '%' then
--     tokenAntiquotFn c s
--   else
--     s

-- def symbol (sym : String) : Parser :=
--   tokenWithAntiquot (symbolNoAntiquot sym)

-- /-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
--     parsing local tokens that have not been added to the token table (but may have
--     been so by some unrelated code).

--     For example, the universe `max` Function is parsed using this combinator so that
--     it can still be used as an identifier outside of universe (but registering it
--     as a token in a Term Syntax would not break the universe Parser). -/
-- def nonReservedSymbolFnAux (sym : String) (errorMsg : String) : ParserFn := fun c s => Id.run do
--   let s := tokenFn [errorMsg] c s
--   if s.hasError then
--     return s
--   match s.stxStack.back with
--   | .atom _ sym' =>
--     if sym == sym' then
--       return s
--   | .ident info rawVal _ _ =>
--     if sym == rawVal.toString then
--       let s := s.popSyntax
--       return s.pushSyntax (Syntax.atom info sym)
--   | _ => ()
--   s.mkUnexpectedTokenError errorMsg

-- def nonReservedSymbolFn (sym : String) : ParserFn :=
--   nonReservedSymbolFnAux sym ("'" ++ sym ++ "'")

-- def nonReservedSymbolInfo (sym : String) (includeIdent : Bool) : ParserInfo := {
--   firstTokens  :=
--     if includeIdent then
--       .tokens [ sym, "ident" ]
--     else
--       .tokens [ sym ]
-- }

-- def nonReservedSymbolNoAntiquot (sym : String) (includeIdent := false) : Parser :=
--   let sym := sym.trim
--   { info := nonReservedSymbolInfo sym includeIdent,
--     fn   := nonReservedSymbolFn sym }

-- def nonReservedSymbol (sym : String) (includeIdent := false) : Parser :=
--   tokenWithAntiquot (nonReservedSymbolNoAntiquot sym includeIdent)

-- /--
--   Define parser for `$e` (if `anonymous == true`) and `$e:name`.
--   `kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.
--   Antiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`. -/
-- @[builtin_doc] def mkAntiquot (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Parser :=
--   let kind := kind ++ (if isPseudoKind then `pseudo else .anonymous) ++ `antiquot
--   let nameP := node `antiquotName <| checkNoWsBefore ("no space before ':" ++ name ++ "'") >> symbol ":" >> nonReservedSymbol name
--   -- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
--   -- antiquotation kind via `noImmediateColon`
--   let nameP := if anonymous then nameP <|> checkNoImmediateColon >> pushNone else nameP
--   -- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
--   leadingNode kind maxPrec <| atomic <|
--     setExpected [] "$" >>
--     manyNoAntiquot (checkNoWsBefore "" >> "$") >>
--     checkNoWsBefore "no space before spliced term" >> antiquotExpr >>
--     nameP

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


-- def numLit : Parser :=
--   Parser.withAntiquot (Parser.mkAntiquot "num" numLitKind)
--   {
--     fn   := expectTokenFn numLitKind "numeral"
--     info := mkAtomicInfo "num"
--   }

-- def decimalLit : Parser := {
--   fn   := expectTokenFn scientificLitKind "scientific number"
--   info := mkAtomicInfo "scientific"
-- }

-- def strLit : Parser := {
--   fn   := expectTokenFn strLitKind "string literal"
--   info := mkAtomicInfo "str"
-- }

-- -- def identifier : Parser := {
-- --   fn   := fun ctx s =>
-- --     let s := tokenFn ["identifier"] ctx s
-- --     if s.hasError then
-- --       s
-- --     else if let .ident _ _ (.str .anonymous _) _ := s.stxStack.back then
-- --       s
-- --     else
-- --       s.mkUnexpectedTokenError "identifier"
-- --   info := mkAtomicInfo "ident"
-- -- }

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
