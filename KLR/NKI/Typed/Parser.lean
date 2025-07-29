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
import Qq

import KLR.NKI.Typed.Common
import KLR.NKI.Typed.PIR

open Lean Parser

/--
Get the position from a `Syntax` and turn it back into a `Syntax` to be embedded in `PIR` AST nodes.

IMPORTANT: Do not call this function on any `Syntax` created by `expand*` function defined in this file.
Because these functions create synthetic holes that don't have position information.
Only call this on `Syntax` passed down from the parser.
-/
def Lean.Syntax.mkPos (stx : Syntax) : Elab.Term.TermElabM (TSyntax `term) := do
  let some startPos := stx.getPos?
    | throwErrorAt stx "cannot get starting position"
  let some endPos := stx.getTailPos?
    | throwErrorAt stx "cannot end ending position"
  let pos := { startPos, endPos : KLR.NKI.Typed.Pos }
  Elab.Term.exprToSyntax (toExpr pos)

def Option.mapSyntax {m α} [Monad m] [MonadQuotation m]
  (f : α → m (TSyntax `term)) : Option α → m (TSyntax `term)
  | some a => do `(Option.some $(← f a))
  | none => `(Option.none)

def List.mapSyntax {m α} [Monad m] [MonadQuotation m]
  (f : α → m (TSyntax `term)) (l : List α) : m (TSyntax `term) := do
  let l ← l.mapM f
  let nil ← `(List.nil)
  l.foldrM (fun hd tl => `(List.cons $hd $tl)) nil

def Lean.Name.toIdentSyntax : Name → Elab.Term.TermElabM (TSyntax `term) :=
  Elab.Term.exprToSyntax ∘ toExpr

def Lean.TSyntax.toIdentSyntax : TSyntax `ident → Elab.Term.TermElabM (TSyntax `term) :=
  Lean.Name.toIdentSyntax ∘ TSyntax.getId

namespace KLR.NKI.Typed.DSL

/-!
# ---------------------------Start of Grammar------------------------------------
-/

/--
NKI type syntax category
-/
declare_syntax_cat nkiType

scoped syntax ident : nkiType
scoped syntax "None" : nkiType
scoped syntax "int" : nkiType
scoped syntax "bool" : nkiType
scoped syntax "float" : nkiType
scoped syntax "str" : nkiType
scoped syntax "tuple[" nkiType,+ "]" : nkiType
scoped syntax "FunctionType[" nkiType,+ "]" : nkiType

/--
NKI expression syntax category
-/
declare_syntax_cat nkiExp

scoped syntax "(" nkiExp ")" : nkiExp

/--
Tuple expressions
-/
scoped syntax "(" nkiExp ", " nkiExp,* ")" : nkiExp

def listElements := leading_parser
  sepBy (categoryParser `nkiExp 0) ", " (allowTrailingSep := true)

/--
List expressions
-/
scoped syntax "[" listElements "]" : nkiExp

-- Values
scoped syntax "None" : nkiExp
scoped syntax "True" : nkiExp
scoped syntax "False" : nkiExp

/--
int literals in NKI
-/
scoped syntax num : nkiExp

/--
Negation
-/
scoped syntax "-" nkiExp : nkiExp

/--
float literals in NKI
-/
scoped syntax scientific : nkiExp

/--
string literals in NKI

TODO: Implement proper Python string literal
-/
scoped syntax str : nkiExp

-- TODO: Add tensor literal support

/--
variables in NKI
-/
scoped syntax ident : nkiExp

/--
Conditional expressions.

These must fit in a single line to avoid conflicts with if-statements
-/
scoped syntax nkiExp !linebreak " if " !linebreak nkiExp !linebreak " else " !linebreak nkiExp : nkiExp

declare_syntax_cat nkiArg

scoped syntax nkiExp : nkiArg
scoped syntax ident "=" nkiExp : nkiArg

/--
Function call expressions with optional type arguments.

Note there must not be linebreaks between the first expression and the arguments.
Otherwise any parenthesized syntax on the next line will be parsed as a function call.
-/
scoped syntax nkiExp !linebreak ("[" nkiType,+ "]")? !linebreak "(" nkiArg,* ")" : nkiExp

-- Logical
scoped syntax:45 nkiExp:45 !linebreak " and " !linebreak nkiExp:46 : nkiExp
scoped syntax:40 nkiExp:40 !linebreak " or " !linebreak nkiExp:41 : nkiExp

-- Comparison
scoped syntax:50 nkiExp:50 !linebreak " == " !linebreak nkiExp:51 : nkiExp
scoped syntax:50 nkiExp:50 !linebreak " != " !linebreak nkiExp:51 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " < " !linebreak nkiExp:56 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " <= " !linebreak nkiExp:56 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " > " !linebreak nkiExp:56 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " >= " !linebreak nkiExp:56 : nkiExp

-- Arithmetic
scoped syntax:50 nkiExp:50 !linebreak " + " !linebreak nkiExp:51 : nkiExp
scoped syntax:50 nkiExp:50 !linebreak " - " !linebreak nkiExp:51 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " * " !linebreak nkiExp:56 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " / " !linebreak nkiExp:56 : nkiExp
scoped syntax:55 nkiExp:55 !linebreak " // " !linebreak nkiExp:56 : nkiExp
scoped syntax:60 nkiExp:60 !linebreak " % " !linebreak nkiExp:61 : nkiExp
scoped syntax:65 nkiExp:65 !linebreak " ** " !linebreak nkiExp:66 : nkiExp

/--
NKI function parameter syntax category
-/
declare_syntax_cat nkiParam

scoped syntax ident (" : " nkiType)? (" = " nkiExp)? : nkiParam

/--
Wildcard parameters for unused function arguments
-/
scoped syntax "_" (" : " nkiType)? (" = " nkiExp)? : nkiParam

declare_syntax_cat nkiIndex

scoped syntax nkiExp : nkiIndex

/--
Slice index
-/
scoped syntax (nkiExp)? ":" (nkiExp)? (":" (nkiExp)?)? : nkiIndex

/--
When parsing `arr[::]`, `::` will get parsed as a single token.
So we need another synax rule to account for that.
-/
scoped syntax (nkiExp)? "::" (nkiExp)? : nkiIndex

scoped syntax "..." : nkiIndex

scoped syntax nkiExp !linebreak "[" nkiIndex,+ "]" : nkiExp

/--
NKI statement syntax category
-/
declare_syntax_cat nkiStmt

/--
Sequence of NKI statements
-/
declare_syntax_cat nkiStmtSeq

def nkiStmtSeq1Idented := leading_parser
  sepBy1Indent (categoryParser `nkiStmt 0) "; " (allowTrailingSep := true)

scoped syntax nkiStmtSeq1Idented : nkiStmtSeq

/--
NKI function definition syntax category
-/
declare_syntax_cat nkiDef

/--
Python decorators for functions
-/
declare_syntax_cat nkiDecorator

scoped syntax "@" ident : nkiDecorator

/--
A function definition
-/
scoped syntax withPosition(
  (nkiDecorator linebreak colEq)?
  "def " ident ("[" ident,+ "]")? "(" nkiParam,* ")" (" -> " nkiType)? ":"
  colGt nkiStmtSeq
) : nkiDef

scoped syntax nkiDef : nkiStmt

/--
Any expression is also a valid statement
-/
scoped syntax nkiExp : nkiStmt

/--
return statements
-/
scoped syntax "return " nkiExp : nkiStmt

/--
Patterns in assignment statements
-/
declare_syntax_cat nkiPat

scoped syntax ident : nkiPat

scoped syntax "_" : nkiPat

scoped syntax "(" nkiPat ")" : nkiPat

/--
Tuple patterns
-/
scoped syntax nkiPat ", " nkiPat,* : nkiPat


/--
Assignment right-hand side that allows unparenthesized tuples
-/
declare_syntax_cat nkiAssignRhs

/--
Regular expressions are valid on RHS
-/
scoped syntax nkiExp : nkiAssignRhs

/--
Unparenthesized tuples are only allowed on RHS of assignments
-/
scoped syntax nkiExp ", " nkiExp,* : nkiAssignRhs

/--
Variable assignments, these are treated as let-bindings

These must not have linebreaks in between
-/
scoped syntax nkiPat !linebreak (" : " !linebreak nkiType)? !linebreak " = " !linebreak nkiAssignRhs : nkiStmt

/--
Conditional statements with optional else clause and elifs

TODO: The linebreak behavior is different than python
-/
scoped syntax withPosition(
  "if " nkiExp ":" linebreak
    (colGt nkiStmtSeq)
  (colEq "elif " nkiExp ":" linebreak
    colGt nkiStmtSeq)*
  (colEq "else:" linebreak
    colGt nkiStmtSeq)?
) : nkiStmt

/--
For-loop statements with iterator binding

TODO: The linebreak behavior is different than python
-/
scoped syntax withPosition(
  "for " ident " in " nkiExp ":" linebreak
    colGt nkiStmtSeq
) : nkiStmt

/--
While-loop statements with condition

TODO: The linebreak behavior is different than python
-/
scoped syntax withPosition(
  "while " nkiExp ":" linebreak
    colGt nkiStmtSeq
) : nkiStmt

scoped syntax "break" : nkiStmt
scoped syntax "continue" : nkiStmt

/--
Python imports syntax category. These are currently ignored during elaboration.
-/
declare_syntax_cat nkiImport

scoped syntax "import " !linebreak ident (!linebreak " as " !linebreak ident)? : nkiImport
scoped syntax "from " !linebreak ident !linebreak " import " !linebreak ident (!linebreak " as " !linebreak ident)? : nkiImport

/--
Top-level declarations in a NKI file.
In Python, this is basically the statement syntax category.
But we want to restrict what can go in here.
-/
declare_syntax_cat nkiDecl

scoped syntax nkiDef : nkiDecl
scoped syntax nkiImport : nkiDecl

declare_syntax_cat nkiFile
scoped syntax nkiDecl* : nkiFile

/-!
# ---------------------------End of Grammar------------------------------------
-/

/-!
# ---------------------------Start of Macro------------------------------------
-/

open Elab Term

partial def expandTyp (stx : TSyntax `nkiType) : TermElabM (TSyntax `term) := do
  let pos ← stx.raw.mkPos
  let typ ←
    match stx with
    | `(nkiType| $i:ident) => do
      let i ← i.toIdentSyntax
      `(PIR.Typ'.var $i)
    | `(nkiType| None) => `(PIR.Typ'.prim Prim.none)
    | `(nkiType| bool) => `(PIR.Typ'.prim Prim.bool)
    | `(nkiType| int) => `(PIR.Typ'.prim (Prim.numeric Numeric.int))
    | `(nkiType| float) => `(PIR.Typ'.prim (Prim.numeric Numeric.float))
    | `(nkiType| string) => `(PIR.Typ'.prim Prim.string)
    | `(nkiType| tuple[$[$ts],*]) => do
      let ts ← ts.toList.mapSyntax expandTyp
      `(PIR.Typ'.tuple $ts)
    | `(nkiType| FunctionType[ $[$ts],* ]) => do
      ts.pop.foldrM
        (fun dom cod => do `(PIR.Typ'.arrow $(← expandTyp dom) $cod))
        (← expandTyp ts.back!)
    | _ => throwUnsupportedSyntax
  `(PIR.Typ.mk $pos $typ)

mutual

partial def expandIndex : TSyntax `nkiIndex → TermElabM (TSyntax `term)
  | `(nkiIndex| $i:nkiExp) => do
    let i ← expandExp i
    `(PIR.Index.coord $i)
  | `(nkiIndex| ...) => `(PIR.Index.ellipsis)
  | `(nkiIndex| $[$l:nkiExp]? : $[$u:nkiExp]? $[: $[$step:nkiExp]?]?) => do
    let l ← l.mapSyntax expandExp
    let u ← u.mapSyntax expandExp
    let step ← (step.getD none).mapSyntax expandExp
    `(PIR.Index.slice $l $u $step)
  | `(nkiIndex| $[$l:nkiExp]? :: $[$step:nkiExp]?) => do
    let l ← l.mapSyntax expandExp
    let step ← step.mapSyntax expandExp
    `(PIR.Index.slice $l Option.none $step)
  | _ => throwUnsupportedSyntax

partial def mkApp
  (f : TSyntax `nkiExp)
  (typArgs : Array (TSyntax `nkiType))
  (args : Array (TSyntax `nkiArg))
  : TermElabM (TSyntax `term) := do
  let pos ← f.raw.mkPos
  let f ← expandExp f
  let typArgs ← typArgs.toList.mapSyntax expandTyp
  let args ← args.toList.mapSyntax (fun (arg : TSyntax `nkiArg) => do
    match arg with
    | `(nkiArg| $e:nkiExp) => do
      let e ← expandExp e
      `(PIR.Arg.mk Option.none $e)
    | `(nkiArg| $i:ident=$e:nkiExp) => do
      let i ← i.toIdentSyntax
      let e ← expandExp e
      `(PIR.Arg.mk (Option.some $i) $e)
    | _ => throwUnsupportedSyntax
  )
  `(PIR.Exp.mk $pos (PIR.Exp'.app $f $typArgs $args))

partial def mkApp1 (pos : TSyntax `term) (f : TSyntax `term) (e : TSyntax `nkiExp) : TermElabM (TSyntax `term) := do
  let e ← expandExp e
  `(PIR.Exp.mk $pos (PIR.Exp'.app $f [] [PIR.Arg.mk Option.none $e]))

partial def mkApp2 (pos : TSyntax `term) (f : TSyntax `term) (e1 : TSyntax `nkiExp) (e2 : TSyntax `nkiExp) : TermElabM (TSyntax `term) := do
  let e1 ← expandExp e1
  let e2 ← expandExp e2
  `(PIR.Exp.mk $pos (PIR.Exp'.app $f [] [PIR.Arg.mk Option.none $e1, PIR.Arg.mk Option.none $e2]))

partial def expandExp (stx : TSyntax `nkiExp) : TermElabM (TSyntax `term) := do
  let pos ← stx.raw.mkPos
  match stx with
  | `(nkiExp| ($e:nkiExp)) => expandExp e
  | `(nkiExp| ($e:nkiExp, $[$es:nkiExp],*)) => do
    let es := #[e].append es
    let es ← es.toList.mapSyntax expandExp
    `(PIR.Exp.mk $pos (PIR.Exp'.tuple $es))
  | `(nkiExp| [$[$es:nkiExp],* ]) => do
    let es ← es.toList.mapSyntax expandExp
    `(PIR.Exp.mk $pos (PIR.Exp'.list $es))
  | `(nkiExp| $i:ident) => do
    let i ← i.toIdentSyntax
    `(PIR.Exp.mk $pos (PIR.Exp'.var $i))
  | `(nkiExp| None) => `(PIR.Exp.mk $pos (PIR.Exp'.value <| PIR.Value.none))
  | `(nkiExp| True) => `(PIR.Exp.mk $pos (PIR.Exp'.value <| PIR.Value.bool true))
  | `(nkiExp| False) => `(PIR.Exp.mk $pos (PIR.Exp'.value <| PIR.Value.bool false))
  | `(nkiExp| $n:num) => `(PIR.Exp.mk $pos (PIR.Exp'.value <| PIR.Value.int $n))
  | `(nkiExp| $n:scientific) => `(PIR.Exp.mk $pos (PIR.Exp'.value <| PIR.Value.float $n))
  | `(nkiExp| $s:str) => `(PIR.Exp.mk $pos (PIR.Exp'.value <| PIR.Value.string $s))
  | `(nkiExp| $f:nkiExp $[[$[$typArgs],*]]? ($[$args],*)) => mkApp f (typArgs.getD #[]) args
  | `(nkiExp| $e:nkiExp[$[$indices],*]) => do
    let e ← expandExp e
    let indices ← indices.toList.mapSyntax expandIndex
    `(PIR.Exp.mk $pos (PIR.Exp'.access $e $indices))
  | `(nkiExp| $thn:nkiExp if $flag:nkiExp else $els:nkiExp) => do
    let flag ← expandExp flag
    let thn ← expandExp thn
    let els ← expandExp els
    `(PIR.Exp.mk $pos (PIR.Exp'.ifExp $flag $thn $els))
  | `(nkiExp| -$e:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.neg))
    mkApp1 pos f e
  | `(nkiExp| $e1:nkiExp and $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.land))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp or $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.lor))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp == $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.eq))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp != $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.ne))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp < $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.lt))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp <= $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.le))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp > $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.gt))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp >= $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.ge))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp + $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.add))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp - $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.sub))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp * $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.mul))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp / $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.div))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp // $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.floor))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp % $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.mod))
    mkApp2 pos f e1 e2
  | `(nkiExp| $e1:nkiExp ** $e2:nkiExp) => do
    let f ← `(PIR.Exp.mk $pos (PIR.Exp'.builtin PIR.Builtin.pow))
    mkApp2 pos f e1 e2
  | _ => throwUnsupportedSyntax

end

partial def expandPat : TSyntax `nkiPat → TermElabM (TSyntax `term)
  | `(nkiPat| $i:ident) => do
    let i ← i.toIdentSyntax
    `(PIR.Pattern.var $i)
  | `(nkiPat| _) => do
    let i ← (`_).toIdentSyntax
    `(PIR.Pattern.var $i)
  | `(nkiPat| ($pat:nkiPat)) => expandPat pat
  | `(nkiPat| $pat:nkiPat, $[$pats:nkiPat],*) => do
    let pats := #[pat].append pats
    let pats ← pats.toList.mapSyntax expandPat
    `(PIR.Pattern.tuple $pats)
  | _ => throwUnsupportedSyntax

def expandAssignRhs (stx : TSyntax `nkiAssignRhs) : TermElabM (TSyntax `term) :=
  match stx with
  | `(nkiAssignRhs| $e:nkiExp) => expandExp e
  | `(nkiAssignRhs| $e:nkiExp, $[$es:nkiExp],*) => do
    let pos ← stx.raw.mkPos
    let es := #[e].append es
    let es ← es.toList.mapSyntax expandExp
    `(PIR.Exp.mk $pos (PIR.Exp'.tuple $es))
  | _ => throwUnsupportedSyntax

mutual

partial def expandDefAux
  (pos : TSyntax `term)
  (name : TSyntax `ident)
  (typParams : Array (TSyntax `ident))
  (params : Array (TSyntax `nkiParam))
  (returns : Option (TSyntax `nkiType))
  (body : TSyntax `nkiStmtSeq)
  (decorator : Option (TSyntax `nkiDecorator))
  : TermElabM (TSyntax `term) := do
  let name ← name.toIdentSyntax
  let typParams ← typParams.toList.mapSyntax TSyntax.toIdentSyntax
  let params ← params.toList.mapSyntax (fun (param : TSyntax `nkiParam) =>
    match param with
    | `(nkiParam| _ $[: $t:nkiType]? $[= $dflt:nkiExp]?) => do
      let i ← (`_).toIdentSyntax
      let t ← t.mapSyntax expandTyp
      let dflt ← dflt.mapSyntax expandExp
      `(PIR.Param.mk $i $t $dflt)
    | `(nkiParam| $i:ident $[: $t:nkiType]? $[= $dflt:nkiExp]?) => do
      let i ← i.toIdentSyntax
      let t ← t.mapSyntax expandTyp
      let dflt ← dflt.mapSyntax expandExp
      `(PIR.Param.mk $i $t $dflt)
    | _ => throwUnsupportedSyntax
  )
  let returns ← returns.mapSyntax expandTyp
  let body ← expandStmtSeq body
  let decorator ← decorator.mapSyntax (fun dec =>
    match dec with
    | `(nkiDecorator| @$i:ident) => i.toIdentSyntax
    | _ => throwUnsupportedSyntax
  )
  `(PIR.Def.mk $pos $name $typParams $params $returns $body $decorator)

partial def expandDef (stx : TSyntax `nkiDef) : TermElabM (TSyntax `term) := do
  let pos ← stx.raw.mkPos
  match stx with
  | `(nkiDef|
      $[
        $dec:nkiDecorator
      ]?
      def $name $[[ $[$typParams],* ]]? ( $[ $params ],* ) $[-> $returns]? : $body
     ) => do
    expandDefAux pos name (typParams.getD #[]) params returns body dec
  | _ => throwUnsupportedSyntax

partial def expandStmtSeq (stx : TSyntax `nkiStmtSeq) : TermElabM (TSyntax `term) := do
  match stx with
  | `(nkiStmtSeq| $[$stmts:nkiStmt]*) => do
    if stmts.isEmpty then
      throwErrorAt stx "cannot have empty statement here"
    else
      let pos ← stx.raw.mkPos
      let stmts ← stmts.mapM expandStmt
      stmts.pop.foldrM
        (fun hd tl => `(PIR.Stmt.mk $pos (PIR.Stmt'.seq $hd $tl)))
        stmts.back!
  | _ => throwUnsupportedSyntax

partial def expandStmt (stx : TSyntax `nkiStmt) : TermElabM (TSyntax `term) := do
  let pos ← stx.raw.mkPos
  let stmt ←
    match stx with
    | `(nkiStmt| $e:nkiExp) => do `(PIR.Stmt'.exp $(← expandExp e))
    | `(nkiStmt| return $e:nkiExp) => do `(PIR.Stmt'.ret $(← expandExp e))
    | `(nkiStmt| $pat:nkiPat $[: $t:nkiType]? = $e:nkiAssignRhs) => do
      let pat ← expandPat pat
      let t ← t.mapSyntax expandTyp
      let e ← expandAssignRhs e
      `(PIR.Stmt'.assign $pat $t $e)
    | `(nkiStmt| $d:nkiDef) => `(PIR.Stmt'.dfn $(← expandDef d))
    | `(nkiStmt|
        if $cond:nkiExp:
          $thn:nkiStmtSeq
        $[
        elif $elifConds:nkiExp:
          $elifBodies:nkiStmtSeq
        ]*
        $[
        else:
          $els:nkiStmtSeq
        ]?
       ) => do
      let cond ← expandExp cond
      let thn ← expandStmtSeq thn
      let elifConds ← elifConds.mapM expandExp
      let elifBodies ← elifBodies.mapM expandStmtSeq
      let elifs ← (elifConds.zip elifBodies).toList.mapSyntax (fun (cond, body) => `(($cond, $body)))
      let els ← els.mapSyntax expandStmtSeq
      `(PIR.Stmt'.ifStm $cond $thn $elifs $els)
    | `(nkiStmt|
        for $i:ident in $iter:nkiExp:
          $body:nkiStmtSeq
       ) => do
      let i ← i.toIdentSyntax
      let iter ← expandExp iter
      let body ← expandStmtSeq body
      `(PIR.Stmt'.forLoop $i $iter $body)
    | `(nkiStmt|
        while $cond:nkiExp:
          $body:nkiStmtSeq
       ) => do
      let cond ← expandExp cond
      let body ← expandStmtSeq body
      `(PIR.Stmt'.whileLoop $cond $body)
    | _ => throwUnsupportedSyntax
  `(PIR.Stmt.mk $pos $stmt)

end

def expandFile (fileName : String) : TSyntax `nkiFile → TermElabM (TSyntax `term)
  | `(nkiFile| $[$decls:nkiDecl]*) => do
    let file := Syntax.mkStrLit fileName
    let decls ← decls.mapM (fun decl =>
      match decl with
      | `(nkiDecl| $_:nkiImport) =>
        -- TODO: properly handle imports
        pure none
      | `(nkiDecl| $dfn:nkiDef) => do
        let dfn ← expandDef dfn
        pure <| some dfn
      | _ => throwUnsupportedSyntax
    )
    let decls ← decls.reduceOption.toList.mapSyntax pure
    `(PIR.Prog.mk $file $decls)
  | _ => throwUnsupportedSyntax

/--
Replace all python line comments with whitespace. We cannot just remove them
since it would mess up source positions. Strings literals written with
single quotes are not handled because we are using Lean's string literal parser.
-/
def whiteOutLineComments (input : String) : String :=
  let chars := input.toList
  let result := whiteOutLineCommentsAux chars false
  String.mk result
where
  whiteOutLineCommentsAux (chars : List Char) (inString : Bool) : List Char :=
    match chars with
    | [] => []
    | '"' :: rest =>
      '"' :: whiteOutLineCommentsAux rest !inString
    | '\\' :: '"' :: rest =>
      -- Escaped quote inside string, don't change string state
      '\\' :: '"' :: whiteOutLineCommentsAux rest inString
    | '#' :: rest =>
      if !inString then
        -- Found comment outside string, replace with spaces until newline
        ' ' :: whiteOutCommentLine rest
      else
        '#' :: whiteOutLineCommentsAux rest inString
    | c :: rest =>
      c :: whiteOutLineCommentsAux rest inString
  whiteOutCommentLine (chars : List Char) : List Char :=
    match chars with
    | [] => []
    | '\n' :: rest => '\n' :: whiteOutLineCommentsAux rest false
    | _ :: rest => ' ' :: whiteOutCommentLine rest

namespace Tests
  -- Test cases for whiteOutLineComments
  def test1 : String :=     "print(\"hello\") # this is a comment"
  def expected1 : String := "print(\"hello\")                    "
  def test2 : String :=     "x = \"string with # inside\" # comment"
  def expected2 : String := "x = \"string with # inside\"          "
  def test3 : String :=     "y = \"escaped \\\" quote\" # comment"
  def expected3 : String := "y = \"escaped \\\" quote\"          "
  def test4 : String :=     "# full line comment\nprint(\"hello\")"
  def expected4 : String := "                   \nprint(\"hello\")"
  #guard whiteOutLineComments test1 == expected1
  #guard whiteOutLineComments test2 == expected2
  #guard whiteOutLineComments test3 == expected3
  #guard whiteOutLineComments test4 == expected4
end Tests

def expandPythonFromString (fileName : String) (input : String) : TermElabM (TSyntax `term) := do
  let input :=  whiteOutLineComments input
  activateScoped `KLR.NKI.Typed.DSL
  let env ← getEnv
  let parsed ← runParserCategory env `nkiFile input
  expandFile fileName ⟨parsed⟩

/-!
# ---------------------------End of Macro--------------------------------------
-/

open Qq in
def parsePythonFromString (fileName : String) (input : String) : CoreM PIR.Prog := unsafe do
  let prog : TermElabM PIR.Prog := do
    let parsed ← (expandPythonFromString fileName input)
    Term.evalTerm PIR.Prog q(PIR.Prog) parsed
  let res ← prog.run.run
  return res.1.1

def parsePythonFile (fileName : String) : IO (Except String PIR.Prog) := do
  let python ← IO.FS.readFile fileName

  -- TODO: This only works when running with `lake exe`.
  -- We must properly link the right `olean` files to make a stand-alone executable
  initSearchPath (← getBuildDir)
  let env ← importModules #[{module := `KLR.NKI.Typed.Parser}] {} (loadExts := true)

  let pEIO : EIO Exception (PIR.Prog × Core.State) :=
    (parsePythonFromString fileName python).run
      {fileName := fileName, fileMap := python.toFileMap}
      {env}

  match ← pEIO.toBaseIO with
  | .ok (prog, _) => return .ok prog
  | .error ex =>
    let fmt ← ex.toMessageData.format
    return .error s!"{fmt}"
