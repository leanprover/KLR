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

import KLR.Compile.Pass
import KLR.NKI.Typed.Python.Basic
import KLR.NKI.Typed.Python.ParserUtil
import KLR.NKI.Typed.Python.PrettyPrint

namespace KLR.NKI.Typed.Python.Parser

open Lean
open KLR.Core (Pos)
open KLR.Compile.Pass (Pass PosError PassM)

/-!
# Python Parser based on python.gram

This implements a full Python parser following the official Python grammar
from python.gram. The parser is structured to match the grammar rules closely.
-/

-- Syntax node kinds for different Python constructs
abbrev fileKind : SyntaxNodeKind := `file
abbrev stmtKind : SyntaxNodeKind := `stmt
abbrev stmtsKind : SyntaxNodeKind := `stmts
abbrev simpleStmtKind : SyntaxNodeKind := `simpleStmt
abbrev compoundStmtKind : SyntaxNodeKind := `compoundStmt
abbrev expKind : SyntaxNodeKind := `exp
abbrev atomKind : SyntaxNodeKind := `atom
abbrev nameKind : SyntaxNodeKind := `name
abbrev numberKind : SyntaxNodeKind := `number
abbrev stringKind : SyntaxNodeKind := `string
abbrev blockKind : SyntaxNodeKind := `block
abbrev funcDefKind : SyntaxNodeKind := `funcDef
abbrev classDefKind : SyntaxNodeKind := `classDef
abbrev ifStmtKind : SyntaxNodeKind := `ifStmt
abbrev whileStmtKind : SyntaxNodeKind := `whileStmt
abbrev forStmtKind : SyntaxNodeKind := `forStmt
abbrev withStmtKind : SyntaxNodeKind := `withStmt
abbrev tryStmtKind : SyntaxNodeKind := `tryStmt
abbrev matchStmtKind : SyntaxNodeKind := `matchStmt
abbrev assignmentKind : SyntaxNodeKind := `assignment
abbrev returnStmtKind : SyntaxNodeKind := `returnStmt
abbrev importStmtKind : SyntaxNodeKind := `importStmt
abbrev raiseStmtKind : SyntaxNodeKind := `raiseStmt
abbrev delStmtKind : SyntaxNodeKind := `delStmt
abbrev yieldStmtKind : SyntaxNodeKind := `yieldStmt
abbrev assertStmtKind : SyntaxNodeKind := `assertStmt
abbrev globalStmtKind : SyntaxNodeKind := `globalStmt
abbrev nonlocalStmtKind : SyntaxNodeKind := `nonlocalStmt
abbrev passStmtKind : SyntaxNodeKind := `passStmt
abbrev breakStmtKind : SyntaxNodeKind := `breakStmt
abbrev continueStmtKind : SyntaxNodeKind := `continueStmt

-- Helper function for Pratt parser
def prattParserAntiquot (kind : Name) (name : String) (parsingTables : PrattParsingTables) : ParserFn :=
  prattParser kind parsingTables .default (mkAntiquot name kind false true).fn

def precCache (kind : Name) (pFn : ParserFn) (expected : List String) (prec : Nat) : Parser :=
  setExpected expected
    {fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn kind pFn)}

-- Indentation-aware separator
@[builtin_doc, inline] def sepBy1Indent (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  let p := Parser.withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  Parser.withPosition <|
    Parser.sepBy1
      (Parser.checkColGe >> p)
      sep
      (psep <|> Parser.checkColEq >> Parser.checkLinebreakBefore >> Parser.pushNone)
      allowTrailingSep

namespace Parse

-- Basic atoms
def pName : Parser := identNoAntiquot
def pNumber : Parser := numLit
def pString : Parser := leading_parser strLitKind

-- Keywords
def pTrue : Parser := symbol "True"
def pFalse : Parser := symbol "False"
def pNone : Parser := symbol "None"
def pEllipsis : Parser := symbol "..."

-- Operators
def pPlus : Parser := symbol "+"
def pMinus : Parser := symbol "-"
def pStar : Parser := symbol "*"
def pSlash : Parser := symbol "/"
def pPercent : Parser := symbol "%"
def pDoubleSlash : Parser := symbol "//"
def pDoubleStar : Parser := symbol "**"
def pAt : Parser := symbol "@"
def pAmpersand : Parser := symbol "&"
def pPipe : Parser := symbol "|"
def pCaret : Parser := symbol "^"
def pTilde : Parser := symbol "~"
def pLeftShift : Parser := symbol "<<"
def pRightShift : Parser := symbol ">>"

-- Comparison operators
def pEq : Parser := symbol "=="
def pNe : Parser := symbol "!="
def pLt : Parser := symbol "<"
def pLe : Parser := symbol "<="
def pGt : Parser := symbol ">"
def pGe : Parser := symbol ">="
def pIs : Parser := symbol "is"
def pIn : Parser := symbol "in"
def pNot : Parser := symbol "not"

-- Assignment operators
def pAssign : Parser := symbol "="
def pPlusAssign : Parser := symbol "+="
def pMinusAssign : Parser := symbol "-="
def pStarAssign : Parser := symbol "*="
def pSlashAssign : Parser := symbol "/="
def pPercentAssign : Parser := symbol "%="
def pDoubleSlashAssign : Parser := symbol "//="
def pDoubleStarAssign : Parser := symbol "**="
def pAtAssign : Parser := symbol "@="
def pAmpersandAssign : Parser := symbol "&="
def pPipeAssign : Parser := symbol "|="
def pCaretAssign : Parser := symbol "^="
def pLeftShiftAssign : Parser := symbol "<<="
def pRightShiftAssign : Parser := symbol ">>="

-- Delimiters
def pLParen : Parser := symbol "("
def pRParen : Parser := symbol ")"
def pLBracket : Parser := symbol "["
def pRBracket : Parser := symbol "]"
def pLBrace : Parser := symbol "{"
def pRBrace : Parser := symbol "}"
def pComma : Parser := symbol ","
def pColon : Parser := symbol ":"
def pSemicolon : Parser := symbol ";"
def pDot : Parser := symbol "."
def pArrow : Parser := symbol "->"

-- Keywords for statements
def pDef : Parser := symbol "def"
def pClass : Parser := symbol "class"
def pIf : Parser := symbol "if"
def pElif : Parser := symbol "elif"
def pElse : Parser := symbol "else"
def pWhile : Parser := symbol "while"
def pFor : Parser := symbol "for"
def pWith : Parser := symbol "with"
def pTry : Parser := symbol "try"
def pExcept : Parser := symbol "except"
def pFinally : Parser := symbol "finally"
def pMatch : Parser := symbol "match"
def pCase : Parser := symbol "case"
def pReturn : Parser := symbol "return"
def pImport : Parser := symbol "import"
def pFrom : Parser := symbol "from"
def pAs : Parser := symbol "as"
def pRaise : Parser := symbol "raise"
def pDel : Parser := symbol "del"
def pYield : Parser := symbol "yield"
def pAssert : Parser := symbol "assert"
def pGlobal : Parser := symbol "global"
def pNonlocal : Parser := symbol "nonlocal"
def pPass : Parser := symbol "pass"
def pBreak : Parser := symbol "break"
def pContinue : Parser := symbol "continue"
def pLambda : Parser := symbol "lambda"
def pAnd : Parser := symbol "and"
def pOr : Parser := symbol "or"
def pAsync : Parser := symbol "async"
def pAwait : Parser := symbol "await"

-- Atom parser - basic literals and names
unsafe def pAtom : Parser :=
  p 0
where
  name := leading_parser:maxPrec pName
  number := leading_parser:maxPrec pNumber
  string := leading_parser:maxPrec pString
  true_lit := leading_parser:maxPrec pTrue
  false_lit := leading_parser:maxPrec pFalse
  none_lit := leading_parser:maxPrec pNone
  ellipsis := leading_parser:maxPrec pEllipsis

  -- Parenthesized expressions, tuples, generators
  group := leading_parser:maxPrec (pLParen >> pExpression >> pRParen)
  tuple := leading_parser:maxPrec (pLParen >> Parser.optional (pStarNamedExpression >> pComma >> Parser.optional pStarNamedExpressions) >> pRParen)
  genexp := leading_parser:maxPrec (pLParen >> (pAssignmentExpression <|> (pExpression >> Parser.notFollowedBy ":=")) >> pForIfClauses >> pRParen)

  -- Lists and list comprehensions
  list := leading_parser:maxPrec (pLBracket >> Parser.optional pStarNamedExpressions >> pRBracket)
  listcomp := leading_parser:maxPrec (pLBracket >> pNamedExpression >> pForIfClauses >> pRBracket)

  -- Dicts, sets, and comprehensions
  dict := leading_parser:maxPrec (pLBrace >> Parser.optional pDoubleStarredKvpairs >> pRBrace)
  set := leading_parser:maxPrec (pLBrace >> pStarNamedExpressions >> pRBrace)
  dictcomp := leading_parser:maxPrec (pLBrace >> pKvpair >> pForIfClauses >> pRBrace)
  setcomp := leading_parser:maxPrec (pLBrace >> pNamedExpression >> pForIfClauses >> pRBrace)

  parsingTables := {
    leadingTable := {
      (identKind, name, maxPrec),
      (numLitKind, number, maxPrec),
      (strLitKind, string, maxPrec),
      (`«True», true_lit, maxPrec),
      (`«False», false_lit, maxPrec),
      (`«None», none_lit, maxPrec),
      (`«...», ellipsis, maxPrec),
      (`«(», group, maxPrec),
      (`«[», list, maxPrec),
      (`«{», dict, maxPrec)
    }
  }
  pFn := prattParserAntiquot atomKind "atom" parsingTables
  p := precCache atomKind pFn ["atom"]

-- Forward declarations for mutual recursion
unsafe def pExpression : Parser := sorry
unsafe def pNamedExpression : Parser := sorry
unsafe def pAssignmentExpression : Parser := sorry
unsafe def pStarNamedExpression : Parser := sorry
unsafe def pStarNamedExpressions : Parser := sorry
unsafe def pForIfClauses : Parser := sorry
unsafe def pKvpair : Parser := sorry
unsafe def pDoubleStarredKvpairs : Parser := sorry
unsafe def pArguments : Parser := sorry
unsafe def pSlices : Parser := sorry

-- Primary expressions - handles attribute access, indexing, calls
unsafe def pPrimary : Parser :=
  p 0
where
  -- Base case - atom
  atom := leading_parser:maxPrec pAtom

  -- Attribute access: primary '.' NAME
  attr := trailing_parser:maxPrec:maxPrec (pDot >> pName)

  -- Function call: primary '(' [arguments] ')'
  call := trailing_parser:maxPrec:maxPrec (pLParen >> Parser.optional pArguments >> pRParen)

  -- Indexing: primary '[' slices ']'
  index := trailing_parser:maxPrec:maxPrec (pLBracket >> pSlices >> pRBracket)

  -- Generator expression: primary genexp
  genexp := trailing_parser:maxPrec:maxPrec pGenexp

  parsingTables := {
    leadingTable := {
      (atomKind, atom, maxPrec)
    },
    trailingTable := {
      (`«.», attr, maxPrec),
      (`«(», call, maxPrec),
      (`«[», index, maxPrec)
    }
  }
  pFn := prattParserAntiquot `primary "primary" parsingTables
  p := precCache `primary pFn ["primary expression"]

-- Await primary - handles await expressions
unsafe def pAwaitPrimary : Parser :=
  p 0
where
  await_expr := leading_parser:maxPrec (pAwait >> pPrimary)
  primary := leading_parser:maxPrec pPrimary

  parsingTables := {
    leadingTable := {
      (`await, await_expr, maxPrec),
      (`primary, primary, maxPrec)
    }
  }
  pFn := prattParserAntiquot `awaitPrimary "awaitPrimary" parsingTables
  p := precCache `awaitPrimary pFn ["await or primary expression"]

-- Power expressions - handles ** operator (right associative)
unsafe def pPower : Parser :=
  p 0
where
  power := trailing_parser:40:39 (pDoubleStar >> pFactor)  -- Right associative
  base := leading_parser:maxPrec pAwaitPrimary

  parsingTables := {
    leadingTable := {
      (`awaitPrimary, base, maxPrec)
    },
    trailingTable := {
      (`«**», power, 40)
    }
  }
  pFn := prattParserAntiquot `power "power" parsingTables
  p := precCache `power pFn ["power expression"]

-- Factor expressions - handles unary +, -, ~
unsafe def pFactor : Parser :=
  p 0
where
  pos := leading_parser:50 (pPlus >> pFactor)
  neg := leading_parser:50 (pMinus >> pFactor)
  invert := leading_parser:50 (pTilde >> pFactor)
  power := leading_parser:maxPrec pPower

  parsingTables := {
    leadingTable := {
      (`«+», pos, 50),
      (`«-», neg, 50),
      (`«~», invert, 50),
      (`power, power, maxPrec)
    }
  }
  pFn := prattParserAntiquot `factor "factor" parsingTables
  p := precCache `factor pFn ["factor expression"]

-- Term expressions - handles *, /, //, %, @
unsafe def pTerm : Parser :=
  p 0
where
  mul := trailing_parser:60:60 (pStar >> pFactor)
  div := trailing_parser:60:60 (pSlash >> pFactor)
  floordiv := trailing_parser:60:60 (pDoubleSlash >> pFactor)
  mod := trailing_parser:60:60 (pPercent >> pFactor)
  matmul := trailing_parser:60:60 (pAt >> pFactor)
  factor := leading_parser:maxPrec pFactor

  parsingTables := {
    leadingTable := {
      (`factor, factor, maxPrec)
    },
    trailingTable := {
      (`«*», mul, 60),
      (`«/», div, 60),
      (`«//», floordiv, 60),
      (`«%», mod, 60),
      (`«@», matmul, 60)
    }
  }
  pFn := prattParserAntiquot `term "term" parsingTables
  p := precCache `term pFn ["term expression"]

-- Sum expressions - handles +, -
unsafe def pSum : Parser :=
  p 0
where
  add := trailing_parser:70:70 (pPlus >> pTerm)
  sub := trailing_parser:70:70 (pMinus >> pTerm)
  term := leading_parser:maxPrec pTerm

  parsingTables := {
    leadingTable := {
      (`term, term, maxPrec)
    },
    trailingTable := {
      (`«+», add, 70),
      (`«-», sub, 70)
    }
  }
  pFn := prattParserAntiquot `sum "sum" parsingTables
  p := precCache `sum pFn ["sum expression"]

-- Shift expressions - handles <<, >>
unsafe def pShiftExpr : Parser :=
  p 0
where
  lshift := trailing_parser:80:80 (pLeftShift >> pSum)
  rshift := trailing_parser:80:80 (pRightShift >> pSum)
  sum := leading_parser:maxPrec pSum

  parsingTables := {
    leadingTable := {
      (`sum, sum, maxPrec)
    },
    trailingTable := {
      (`«<<», lshift, 80),
      (`«>>», rshift, 80)
    }
  }
  pFn := prattParserAntiquot `shiftExpr "shiftExpr" parsingTables
  p := precCache `shiftExpr pFn ["shift expression"]

-- Bitwise AND expressions - handles &
unsafe def pBitwiseAnd : Parser :=
  p 0
where
  and := trailing_parser:90:90 (pAmpersand >> pShiftExpr)
  shift := leading_parser:maxPrec pShiftExpr

  parsingTables := {
    leadingTable := {
      (`shiftExpr, shift, maxPrec)
    },
    trailingTable := {
      (`«&», and, 90)
    }
  }
  pFn := prattParserAntiquot `bitwiseAnd "bitwiseAnd" parsingTables
  p := precCache `bitwiseAnd pFn ["bitwise and expression"]

-- Bitwise XOR expressions - handles ^
unsafe def pBitwiseXor : Parser :=
  p 0
where
  xor := trailing_parser:100:100 (pCaret >> pBitwiseAnd)
  and := leading_parser:maxPrec pBitwiseAnd

  parsingTables := {
    leadingTable := {
      (`bitwiseAnd, and, maxPrec)
    },
    trailingTable := {
      (`«^», xor, 100)
    }
  }
  pFn := prattParserAntiquot `bitwiseXor "bitwiseXor" parsingTables
  p := precCache `bitwiseXor pFn ["bitwise xor expression"]

-- Bitwise OR expressions - handles |
unsafe def pBitwiseOr : Parser :=
  p 0
where
  or := trailing_parser:110:110 (pPipe >> pBitwiseXor)
  xor := leading_parser:maxPrec pBitwiseXor

  parsingTables := {
    leadingTable := {
      (`bitwiseXor, xor, maxPrec)
    },
    trailingTable := {
      (`«|», or, 110)
    }
  }
  pFn := prattParserAntiquot `bitwiseOr "bitwiseOr" parsingTables
  p := precCache `bitwiseOr pFn ["bitwise or expression"]

-- Comparison expressions - handles ==, !=, <, <=, >, >=, is, in, not in, is not
unsafe def pComparison : Parser :=
  p 0
where
  eq := trailing_parser:120:120 (pEq >> pBitwiseOr)
  ne := trailing_parser:120:120 (pNe >> pBitwiseOr)
  lt := trailing_parser:120:120 (pLt >> pBitwiseOr)
  le := trailing_parser:120:120 (pLe >> pBitwiseOr)
  gt := trailing_parser:120:120 (pGt >> pBitwiseOr)
  ge := trailing_parser:120:120 (pGe >> pBitwiseOr)
  is_op := trailing_parser:120:120 (pIs >> pBitwiseOr)
  in_op := trailing_parser:120:120 (pIn >> pBitwiseOr)
  not_in := trailing_parser:120:120 (pNot >> pIn >> pBitwiseOr)
  is_not := trailing_parser:120:120 (pIs >> pNot >> pBitwiseOr)
  bitwise_or := leading_parser:maxPrec pBitwiseOr

  parsingTables := {
    leadingTable := {
      (`bitwiseOr, bitwise_or, maxPrec)
    },
    trailingTable := {
      (`«==», eq, 120),
      (`«!=», ne, 120),
      (`«<», lt, 120),
      (`«<=», le, 120),
      (`«>», gt, 120),
      (`«>=», ge, 120),
      (`is, is_op, 120),
      (`in, in_op, 120)
    }
  }
  pFn := prattParserAntiquot `comparison "comparison" parsingTables
  p := precCache `comparison pFn ["comparison expression"]

-- Inversion expressions - handles 'not'
unsafe def pInversion : Parser :=
  p 0
where
  not_expr := leading_parser:130 (pNot >> pInversion)
  comparison := leading_parser:maxPrec pComparison

  parsingTables := {
    leadingTable := {
      (`not, not_expr, 130),
      (`comparison, comparison, maxPrec)
    }
  }
  pFn := prattParserAntiquot `inversion "inversion" parsingTables
  p := precCache `inversion pFn ["inversion expression"]

-- Conjunction expressions - handles 'and'
unsafe def pConjunction : Parser :=
  p 0
where
  and := trailing_parser:140:140 (pAnd >> pInversion)
  inversion := leading_parser:maxPrec pInversion

  parsingTables := {
    leadingTable := {
      (`inversion, inversion, maxPrec)
    },
    trailingTable := {
      (`and, and, 140)
    }
  }
  pFn := prattParserAntiquot `conjunction "conjunction" parsingTables
  p := precCache `conjunction pFn ["conjunction expression"]

-- Disjunction expressions - handles 'or'
unsafe def pDisjunction : Parser :=
  p 0
where
  or := trailing_parser:150:150 (pOr >> pConjunction)
  conjunction := leading_parser:maxPrec pConjunction

  parsingTables := {
    leadingTable := {
      (`conjunction, conjunction, maxPrec)
    },
    trailingTable := {
      (`or, or, 150)
    }
  }
  pFn := prattParserAntiquot `disjunction "disjunction" parsingTables
  p := precCache `disjunction pFn ["disjunction expression"]

-- Lambda expressions
unsafe def pLambdef : Parser :=
  leading_parser (pLambda >> Parser.optional pLambdaParams >> pColon >> pExpression)

-- Lambda parameters (simplified version)
unsafe def pLambdaParams : Parser :=
  Parser.sepBy pName pComma

-- Assignment expressions - handles :=
unsafe def pAssignmentExpression : Parser :=
  leading_parser (pName >> symbol ":=" >> pExpression)

-- Named expressions - assignment or regular expression
unsafe def pNamedExpression : Parser :=
  pAssignmentExpression <|> (pExpression >> Parser.notFollowedBy ":=")

-- Main expression parser - handles conditional expressions and lambdas
unsafe def pExpression : Parser :=
  p 0
where
  -- Conditional expression: disjunction 'if' disjunction 'else' expression
  conditional := leading_parser:maxPrec (pDisjunction >> pIf >> pDisjunction >> pElse >> pExpression)
  disjunction := leading_parser:maxPrec pDisjunction
  lambda := leading_parser:maxPrec pLambdef

  parsingTables := {
    leadingTable := {
      (`disjunction, disjunction, maxPrec),
      (`lambda, lambda, maxPrec)
    }
  }
  pFn := prattParserAntiquot expKind "expression" parsingTables
  p := precCache expKind pFn ["expression"]

-- Star expressions - handles * unpacking
unsafe def pStarExpression : Parser :=
  (pStar >> pBitwiseOr) <|> pExpression

-- Star named expressions
unsafe def pStarNamedExpression : Parser :=
  (pStar >> pBitwiseOr) <|> pNamedExpression

-- Multiple star named expressions
unsafe def pStarNamedExpressions : Parser :=
  Parser.sepBy pStarNamedExpression pComma

-- Expressions (multiple)
unsafe def pExpressions : Parser :=
  Parser.sepBy pExpression pComma

-- Yield expressions
unsafe def pYieldExpr : Parser :=
  (pYield >> pFrom >> pExpression) <|> (pYield >> Parser.optional pStarExpressions)

-- Star expressions (multiple)
unsafe def pStarExpressions : Parser :=
  Parser.sepBy pStarExpression pComma

-- For-if clauses for comprehensions
unsafe def pForIfClauses : Parser :=
  Parser.many1 pForIfClause

unsafe def pForIfClause : Parser :=
  (pAsync >> pFor >> pStarTargets >> pIn >> pDisjunction >> Parser.many (pIf >> pDisjunction)) <|>
  (pFor >> pStarTargets >> pIn >> pDisjunction >> Parser.many (pIf >> pDisjunction))

-- Key-value pairs for dictionaries
unsafe def pKvpair : Parser :=
  pExpression >> pColon >> pExpression

-- Double-starred key-value pairs
unsafe def pDoubleStarredKvpairs : Parser :=
  Parser.sepBy pDoubleStarredKvpair pComma

unsafe def pDoubleStarredKvpair : Parser :=
  (pDoubleStar >> pBitwiseOr) <|> pKvpair

-- Generator expression
unsafe def pGenexp : Parser :=
  pLParen >> (pAssignmentExpression <|> (pExpression >> Parser.notFollowedBy ":=")) >> pForIfClauses >> pRParen

-- Arguments for function calls
unsafe def pArguments : Parser :=
  pArgs >> Parser.optional pComma

unsafe def pArgs : Parser :=
  (Parser.sepBy1 (pStarredExpression <|> (pAssignmentExpression <|> (pExpression >> Parser.notFollowedBy ":="))) pComma >> Parser.optional (pComma >> pKwargs)) <|>
  pKwargs

unsafe def pKwargs : Parser :=
  Parser.sepBy1 pKwargOrDoubleStarred pComma

unsafe def pKwargOrDoubleStarred : Parser :=
  (pName >> pAssign >> pExpression) <|> (pDoubleStar >> pExpression)

unsafe def pStarredExpression : Parser :=
  pStar >> pExpression

-- Slices for indexing
unsafe def pSlices : Parser :=
  (pSlice >> Parser.notFollowedBy pComma) <|>
  Parser.sepBy1 (pSlice <|> pStarredExpression) pComma

unsafe def pSlice : Parser :=
  (Parser.optional pExpression >> pColon >> Parser.optional pExpression >> Parser.optional (pColon >> Parser.optional pExpression)) <|>
  pNamedExpression

-- Star targets for assignments
unsafe def pStarTargets : Parser :=
  (pStarTarget >> Parser.notFollowedBy pComma) <|>
  Parser.sepBy1 pStarTarget pComma

unsafe def pStarTarget : Parser :=
  (pStar >> pStarTarget) <|> pTargetWithStarAtom

unsafe def pTargetWithStarAtom : Parser :=
  (pTPrimary >> pDot >> pName) <|>
  (pTPrimary >> pLBracket >> pSlices >> pRBracket) <|>
  pStarAtom

unsafe def pStarAtom : Parser :=
  pName <|>
  (pLParen >> pTargetWithStarAtom >> pRParen) <|>
  (pLParen >> Parser.optional pStarTargetsTupleSeq >> pRParen) <|>
  (pLBracket >> Parser.optional pStarTargetsListSeq >> pRBracket)

unsafe def pStarTargetsTupleSeq : Parser :=
  Parser.sepBy1 pStarTarget pComma

unsafe def pStarTargetsListSeq : Parser :=
  Parser.sepBy1 pStarTarget pComma

unsafe def pTPrimary : Parser :=
  p 0
where
  attr := trailing_parser:maxPrec:maxPrec (pDot >> pName)
  index := trailing_parser:maxPrec:maxPrec (pLBracket >> pSlices >> pRBracket)
  call := trailing_parser:maxPrec:maxPrec (pLParen >> Parser.optional pArguments >> pRParen)
  genexp := trailing_parser:maxPrec:maxPrec pGenexp
  atom := leading_parser:maxPrec pAtom

  parsingTables := {
    leadingTable := {
      (atomKind, atom, maxPrec)
    },
    trailingTable := {
      (`«.», attr, maxPrec),
      (`«[», index, maxPrec),
      (`«(», call, maxPrec)
    }
  }
  pFn := prattParserAntiquot `tPrimary "tPrimary" parsingTables
  p := precCache `tPrimary pFn ["target primary"]

-- Block parser - handles indented blocks
unsafe def pBlock : Parser :=
  (Parser.symbol "NEWLINE" >> Parser.symbol "INDENT" >> pStatements >> Parser.symbol "DEDENT") <|>
  pSimpleStmts

-- Simple statements
unsafe def pSimpleStmt : Parser :=
  p 0
where
  assignment := leading_parser:maxPrec pAssignment
  type_alias := leading_parser:maxPrec pTypeAlias
  star_expressions := leading_parser:maxPrec pStarExpressions
  return_stmt := leading_parser:maxPrec pReturnStmt
  import_stmt := leading_parser:maxPrec pImportStmt
  raise_stmt := leading_parser:maxPrec pRaiseStmt
  pass_stmt := leading_parser:maxPrec pPass
  del_stmt := leading_parser:maxPrec pDelStmt
  yield_stmt := leading_parser:maxPrec pYieldStmt
  assert_stmt := leading_parser:maxPrec pAssertStmt
  break_stmt := leading_parser:maxPrec pBreak
  continue_stmt := leading_parser:maxPrec pContinue
  global_stmt := leading_parser:maxPrec pGlobalStmt
  nonlocal_stmt := leading_parser:maxPrec pNonlocalStmt

  parsingTables := {
    leadingTable := {
      (`assignment, assignment, maxPrec),
      (`return, return_stmt, maxPrec),
      (`import, import_stmt, maxPrec),
      (`from, import_stmt, maxPrec),
      (`raise, raise_stmt, maxPrec),
      (`pass, pass_stmt, maxPrec),
      (`del, del_stmt, maxPrec),
      (`yield, yield_stmt, maxPrec),
      (`assert, assert_stmt, maxPrec),
      (`break, break_stmt, maxPrec),
      (`continue, continue_stmt, maxPrec),
      (`global, global_stmt, maxPrec),
      (`nonlocal, nonlocal_stmt, maxPrec)
    },
    leadingParsers := [
      (star_expressions, maxPrec)
    ]
  }
  pFn := prattParserAntiquot simpleStmtKind "simpleStmt" parsingTables
  p := precCache simpleStmtKind pFn ["simple statement"]

-- Simple statements sequence
unsafe def pSimpleStmts : Parser :=
  (pSimpleStmt >> Parser.notFollowedBy pSemicolon >> Parser.symbol "NEWLINE") <|>
  (Parser.sepBy1 pSimpleStmt pSemicolon >> Parser.optional pSemicolon >> Parser.symbol "NEWLINE")

-- Compound statements
unsafe def pCompoundStmt : Parser :=
  p 0
where
  function_def := leading_parser:maxPrec pFunctionDef
  if_stmt := leading_parser:maxPrec pIfStmt
  class_def := leading_parser:maxPrec pClassDef
  with_stmt := leading_parser:maxPrec pWithStmt
  for_stmt := leading_parser:maxPrec pForStmt
  try_stmt := leading_parser:maxPrec pTryStmt
  while_stmt := leading_parser:maxPrec pWhileStmt
  match_stmt := leading_parser:maxPrec pMatchStmt

  parsingTables := {
    leadingTable := {
      (`def, function_def, maxPrec),
      (`async, function_def, maxPrec),
      (`if, if_stmt, maxPrec),
      (`class, class_def, maxPrec),
      (`with, with_stmt, maxPrec),
      (`for, for_stmt, maxPrec),
      (`try, try_stmt, maxPrec),
      (`while, while_stmt, maxPrec),
      (`match, match_stmt, maxPrec)
    }
  }
  pFn := prattParserAntiquot compoundStmtKind "compoundStmt" parsingTables
  p := precCache compoundStmtKind pFn ["compound statement"]

-- Statement parser
unsafe def pStatement : Parser :=
  pCompoundStmt <|> pSimpleStmts

-- Statements sequence
unsafe def pStatements : Parser :=
  Parser.many1 pStatement

-- Assignment statements
unsafe def pAssignment : Parser :=
  -- Annotated assignment: NAME ':' expression ['=' annotated_rhs]
  (pName >> pColon >> pExpression >> Parser.optional (pAssign >> pAnnotatedRhs)) <|>
  -- Annotated assignment with targets: ('(' single_target ')' | single_subscript_attribute_target) ':' expression ['=' annotated_rhs]
  ((pLParen >> pSingleTarget >> pRParen) >> pColon >> pExpression >> Parser.optional (pAssign >> pAnnotatedRhs)) <|>
  (pSingleSubscriptAttributeTarget >> pColon >> pExpression >> Parser.optional (pAssign >> pAnnotatedRhs)) <|>
  -- Multiple assignment: (star_targets '=')+ (yield_expr | star_expressions) !'=' [TYPE_COMMENT]
  (Parser.many1 (pStarTargets >> pAssign) >> (pYieldExpr <|> pStarExpressions) >> Parser.notFollowedBy pAssign) <|>
  -- Augmented assignment: single_target augassign ~ (yield_expr | star_expressions)
  (pSingleTarget >> pAugassign >> (pYieldExpr <|> pStarExpressions))

unsafe def pAnnotatedRhs : Parser :=
  pYieldExpr <|> pStarExpressions

unsafe def pAugassign : Parser :=
  pPlusAssign <|> pMinusAssign <|> pStarAssign <|> pAtAssign <|> pSlashAssign <|>
  pPercentAssign <|> pAmpersandAssign <|> pPipeAssign <|> pCaretAssign <|>
  pLeftShiftAssign <|> pRightShiftAssign <|> pDoubleStarAssign <|> pDoubleSlashAssign

unsafe def pSingleTarget : Parser :=
  pSingleSubscriptAttributeTarget <|> pName <|> (pLParen >> pSingleTarget >> pRParen)

unsafe def pSingleSubscriptAttributeTarget : Parser :=
  (pTPrimary >> pDot >> pName) <|> (pTPrimary >> pLBracket >> pSlices >> pRBracket)

-- Type alias statements
unsafe def pTypeAlias : Parser :=
  symbol "type" >> pName >> Parser.optional pTypeParams >> pAssign >> pExpression

unsafe def pTypeParams : Parser :=
  pLBracket >> pTypeParamSeq >> pRBracket

unsafe def pTypeParamSeq : Parser :=
  Parser.sepBy1 pTypeParam pComma

unsafe def pTypeParam : Parser :=
  (pName >> Parser.optional pTypeParamBound >> Parser.optional pTypeParamDefault) <|>
  (pStar >> pName >> Parser.optional pTypeParamStarredDefault) <|>
  (pDoubleStar >> pName >> Parser.optional pTypeParamDefault)

unsafe def pTypeParamBound : Parser :=
  pColon >> pExpression

unsafe def pTypeParamDefault : Parser :=
  pAssign >> pExpression

unsafe def pTypeParamStarredDefault : Parser :=
  pAssign >> pStarExpression

-- Return statements
unsafe def pReturnStmt : Parser :=
  pReturn >> Parser.optional pStarExpressions

-- Raise statements
unsafe def pRaiseStmt : Parser :=
  (pRaise >> pExpression >> Parser.optional (pFrom >> pExpression)) <|> pRaise

-- Delete statements
unsafe def pDelStmt : Parser :=
  pDel >> pDelTargets

unsafe def pDelTargets : Parser :=
  Parser.sepBy1 pDelTarget pComma

unsafe def pDelTarget : Parser :=
  (pTPrimary >> pDot >> pName) <|>
  (pTPrimary >> pLBracket >> pSlices >> pRBracket) <|>
  pDelTAtom

unsafe def pDelTAtom : Parser :=
  pName <|>
  (pLParen >> pDelTarget >> pRParen) <|>
  (pLParen >> Parser.optional pDelTargets >> pRParen) <|>
  (pLBracket >> Parser.optional pDelTargets >> pRBracket)

-- Yield statements
unsafe def pYieldStmt : Parser :=
  pYieldExpr

-- Assert statements
unsafe def pAssertStmt : Parser :=
  pAssert >> pExpression >> Parser.optional (pComma >> pExpression)

-- Global statements
unsafe def pGlobalStmt : Parser :=
  pGlobal >> Parser.sepBy1 pName pComma

-- Nonlocal statements
unsafe def pNonlocalStmt : Parser :=
  pNonlocal >> Parser.sepBy1 pName pComma
