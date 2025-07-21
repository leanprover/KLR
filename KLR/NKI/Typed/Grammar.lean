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

import KLR.NKI.Typed.Syntax

namespace KLR.NKI.Typed.DSL

open Lean Parser


/-!
# ---------------------------Start of Grammar------------------------------------
-/

/--
NKI type syntax category
-/
declare_syntax_cat nkiType

scoped syntax "(" nkiType ")" : nkiType
scoped syntax ident : nkiType
scoped syntax "None" : nkiType
scoped syntax "int" : nkiType
scoped syntax "bool" : nkiType
scoped syntax "float" : nkiType
scoped syntax "string" : nkiType
scoped syntax:50 nkiType:51 " -> " nkiType:50 : nkiType

/--
NKI expression syntax category
-/
declare_syntax_cat nkiExpr

scoped syntax "(" nkiExpr ")" : nkiExpr

-- Values
scoped syntax "None" : nkiExpr
scoped syntax "True" : nkiExpr
scoped syntax "False" : nkiExpr
scoped syntax num : nkiExpr -- int
scoped syntax scientific : nkiExpr -- float
scoped syntax str : nkiExpr
-- TODO: Add tensor literal support

-- Expr
scoped syntax ident : nkiExpr -- var

/--
Conditional expressions that must fit on a single line to avoid conflicts with if-statements
-/
scoped syntax nkiExpr !linebreak " if " !linebreak nkiExpr !linebreak " else " !linebreak nkiExpr : nkiExpr

/--
Function call expressions with optional type arguments
-/
scoped syntax nkiExpr ("[" nkiType,* "]")? "(" nkiExpr,* ")" : nkiExpr

scoped syntax "range" : nkiExpr

-- Logical
scoped syntax:45 nkiExpr:45 " and " nkiExpr:46 : nkiExpr
scoped syntax:40 nkiExpr:40 " or " nkiExpr:41 : nkiExpr

-- Comparison
scoped syntax:50 nkiExpr:50 " == " nkiExpr:51 : nkiExpr
scoped syntax:50 nkiExpr:50 " != " nkiExpr:51 : nkiExpr
scoped syntax:55 nkiExpr:55 " < " nkiExpr:56 : nkiExpr
scoped syntax:55 nkiExpr:55 " <= " nkiExpr:56 : nkiExpr
scoped syntax:55 nkiExpr:55 " > " nkiExpr:56 : nkiExpr
scoped syntax:55 nkiExpr:55 " >= " nkiExpr:56 : nkiExpr

-- Arithmetic
scoped syntax:50 nkiExpr:50 " + " nkiExpr:51 : nkiExpr
scoped syntax:50 nkiExpr:50 " - " nkiExpr:51 : nkiExpr
scoped syntax:55 nkiExpr:55 " * " nkiExpr:56 : nkiExpr
scoped syntax:55 nkiExpr:55 " / " nkiExpr:56 : nkiExpr
scoped syntax:55 nkiExpr:55 " // " nkiExpr:56 : nkiExpr
scoped syntax:60 nkiExpr:60 " % " nkiExpr:61 : nkiExpr
scoped syntax:65 nkiExpr:65 " ** " nkiExpr:66 : nkiExpr

-- TODO: Add built-in function support

/--
NKI function parameter syntax category
-/
declare_syntax_cat nkiParam

scoped syntax ident (" : " nkiType)? : nkiParam

/--
Wildcard parameters for unused function arguments
-/
scoped syntax "_" (" : " nkiType)? : nkiParam

/--
NKI statement syntax category
-/
declare_syntax_cat nkiStmt

/--
Sequence of NKI statements
-/
declare_syntax_cat nkiStmtSeq

@[inline] def nkiStmtParser (rbp : Nat := 0) : Parser :=
  categoryParser `nkiStmt rbp

def nkiStmtSeq1Idented := leading_parser
  sepBy1Indent nkiStmtParser "; " (allowTrailingSep := true)

scoped syntax nkiStmtSeq1Idented : nkiStmtSeq

/--
NKI function definition syntax category
-/
declare_syntax_cat nkiDef

scoped syntax withPosition("def " ident ("[" ident,* "]")? "(" nkiParam,* ")" (" -> " nkiType)? ":" colGt nkiStmtSeq) : nkiDef
scoped syntax nkiDef : nkiStmt

scoped syntax nkiExpr : nkiStmt

scoped syntax "return " nkiExpr : nkiStmt

/--
Variable assignments and let-bindings
-/
scoped syntax ident !linebreak (" : " !linebreak nkiType)? !linebreak " = " !linebreak nkiExpr : nkiStmt

/--
Conditional statements with optional else clause
-/
scoped syntax withPosition("if " nkiExpr ":" linebreak (colGt nkiStmtSeq) (colEq "else:" linebreak colGt nkiStmtSeq)?) : nkiStmt

/--
For-loop statements with iterator binding
-/
scoped syntax withPosition("for " ident " in " nkiExpr ":" linebreak colGt nkiStmtSeq) : nkiStmt

/--
While-loop statements with condition
-/
scoped syntax withPosition("while " nkiExpr ":" linebreak colGt nkiStmtSeq) : nkiStmt

scoped syntax "break" : nkiStmt
scoped syntax "continue" : nkiStmt

/-!
# ---------------------------End of Grammar------------------------------------
-/

/-!
# ---------------------------Start of Macro------------------------------------
-/

open Elab Meta

/--
Free variables in an NKI definition, represented as an array of identifiers and their types
-/
abbrev NKIFVars := Array (Ident × TSyntax `term)

structure Context where
  /--
    Names and recursion status of currently parsed definitions.
    The first element refers to the most recently entered definition.
  -/
  funcScopes : List (Ident × Bool) := []
  bvars : Array Ident := #[]
  fvars : NKIFVars := #[]
  /--
    Whether we are at the top level inside a function body.
    Used to determine if an implicit `return None` should be added at the end of a function.
  -/
  atTopLevel : Bool := true

abbrev NKIElabM := StateT Context Elab.TermElabM

namespace NKIElabM

  def pushBVar (v : Ident) : NKIElabM Unit := do
    let c ← get
    set {c with bvars := c.bvars.push v}

  def popBVar : NKIElabM Unit := do
    let c ← get
    set {c with bvars := c.bvars.pop}

  def addFVar (i : Ident) (typ : TSyntax `term) : NKIElabM Unit := do
    let c ← get
    if !(c.fvars.map Prod.snd).contains i then
      set {c with fvars := c.fvars.push (i, typ)}

  def isBound (i : Ident) : NKIElabM Bool := do
    let { bvars, .. } ← get
    return bvars.contains i

  def atTopLevel : NKIElabM Bool := do
    pure (← get).atTopLevel

  def withBVar (i : Ident) (x : NKIElabM α) : NKIElabM α := do
    let c ← get
    set {c with bvars := c.bvars.push i}
    let a ← x
    modifyGet fun c =>
    (a, {c with bvars := c.bvars.pop})

  def withTopLevel {α : Type} (newTopLevel : Bool) (x : NKIElabM α) : NKIElabM α := do
    let c ← get
    let oldTopLevel := c.atTopLevel
    set {c with atTopLevel := newTopLevel}
    let a ← x
    modifyGet fun c =>
    (a, {c with atTopLevel := oldTopLevel})

  def withFunc (name : Ident) (params : Array (Ident × Option (TSyntax `term)))
    (x : NKIElabM α) : NKIElabM (α × Bool) := do
    -- set bound variables
    pushBVar name
    params.forM (fun (p, _) => pushBVar p)
    -- enter function scope
    let c ← get
    set {c with funcScopes := (name, false) :: c.funcScopes}
    -- do monadic action
    let a ← withTopLevel true x
    -- unset bound variables
    popBVar
    params.forM (fun _ => popBVar)
    -- exit function scope
    modifyGet fun c =>
    let recs := c.funcScopes.head!.2
    let s := {c with funcScopes := c.funcScopes.tail}
    ((a, recs), s)

  def checkRec (i : Ident) : NKIElabM Unit := do
    let c ← get
    set {c with funcScopes := go c.funcScopes}
  where
    go
    | [] => []
    | (fn, recs) :: tl =>
      if fn == i then
        (fn, true) :: tl
      else
        (fn, recs) :: go tl

end NKIElabM

def Command.liftNKIElabM {α : Type} (x : NKIElabM α) : Command.CommandElabM (α × Context) :=
  Command.liftTermElabM <| StateT.run x {}

def Term.liftNKIElabM {α : Type} (x : NKIElabM α) : Term.TermElabM (α × Context) :=
  StateT.run x {}

def nkiTypeToSyntaxAux (bvars : List Ident) : Lean.Expr → NKIElabM (TSyntax `term)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.none []) =>
    `(Typ.prim Prim.none)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.bool []) =>
    `(Typ.prim Prim.bool)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (mkApp (.const `KLR.NKI.Typed.Prim.numeric []) (.const `KLR.NKI.Typed.Numeric.int [])) =>
    `(Typ.prim (Prim.numeric Numeric.int))
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (mkApp (.const `KLR.NKI.Typed.Prim.numeric []) (.const `KLR.NKI.Typed.Numeric.float [])) =>
    `(Typ.prim (Prim.numeric Numeric.float))
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.string []) =>
    `(Typ.prim Prim.string)
  | mkApp3 (.const `KLR.NKI.Typed.Typ.arrow []) _ t1 t2 => do
    let t1 ← nkiTypeToSyntaxAux bvars t1
    let t2 ← nkiTypeToSyntaxAux bvars t2
    `(Typ.arrow $t1 $t2)
  | mkApp4 (.const `KLR.NKI.Typed.Typ.all []) _ _ _ (.lam name _ body _) => do
    let body ← nkiTypeToSyntaxAux (mkIdent name :: bvars) body
    `(Typ.all (fun $(mkIdent name) => $body))
  | mkApp3 (.const `KLR.NKI.Typed.Typ.var []) _ _ (.bvar i) => do
    let id := bvars[i]!
    `(Typ.var $id)
  | _ => throwError "unsupported NKI type definition"

/--
Convert a `Lean.Expr` representing an `NKI.Typed.Typ` into `Lean.Syntax`.
Used for defining free variables in NKI statements.
-/
def nkiTypeToSyntax (e : Lean.Expr) : NKIElabM (TSyntax `term) :=
  nkiTypeToSyntaxAux [] e

partial def expandNKIType : TSyntax `nkiType → NKIElabM (TSyntax `term)
  | `(nkiType| ($t:nkiType)) => expandNKIType t
  | `(nkiType| $i:ident) => `(Typ.var $i)
  | `(nkiType| None) => `(Typ.prim Prim.none)
  | `(nkiType| bool) => `(Typ.prim Prim.bool)
  | `(nkiType| int) => `(Typ.prim (Prim.numeric Numeric.int))
  | `(nkiType| float) => `(Typ.prim (Prim.numeric Numeric.float))
  | `(nkiType| string) => `(Typ.prim Prim.string)
  | `(nkiType| $t1:nkiType -> $t2:nkiType) => do
    `(Typ.arrow $(← expandNKIType t1) $(← expandNKIType t2))
  | _ => throwUnsupportedSyntax

mutual

partial def mkNKIApp
  (f : TSyntax `nkiExpr)
  (typArgs : Array (TSyntax `nkiType))
  (args : Array (TSyntax `nkiExpr))
  : NKIElabM (TSyntax `term) := do
  let f ← expandNKIExpr f
  let typArgs ← typArgs.mapM expandNKIType
  let args ← args.mapM expandNKIExpr
  (← typArgs.foldlM (fun f arg => `(Expr.typApp $f $arg (by solve_subst))) f)
    |> args.foldlM (fun f arg => `(Expr.app $f $arg))

partial def mkNKIApp2 (f : TSyntax `term) (e1 : TSyntax `nkiExpr) (e2 : TSyntax `nkiExpr) : NKIElabM (TSyntax `term) := do
  let e1 ← expandNKIExpr e1
  let e2 ← expandNKIExpr e2
  `(Expr.app (Expr.app $f $e1) $e2)

partial def expandNKIExpr : TSyntax `nkiExpr → NKIElabM (TSyntax `term)
  | `(nkiExpr| ($e:nkiExpr)) => expandNKIExpr e
  | `(nkiExpr| $i:ident) => do
    /-
    Identifiers require special handling.

    If the identifier is a currently bound variable in the NKI statement,
    no special processing is needed.

    If it is not bound, we check if it exists in the Lean context,
    retrieve its type, and record it as a free variable in `Context`.
    The top-level elaboration will then add the appropriate `fvar` declarations
    to the preamble of the NKI statement.
    -/
    if !(← NKIElabM.isBound i) then
      let expr ← Term.elabTerm i .none
      let type ← inferType expr
      if type.isAppOf `KLR.NKI.Typed.Kernel then
        check expr; check type
        let type := type.getAppArgs[3]!
        NKIElabM.addFVar i (← nkiTypeToSyntax type)
      else
        Lean.throwErrorAt i s!"{i} has type {type}, expected a NKI Kernel"
    NKIElabM.checkRec i
    `(Expr.var $i)
  | `(nkiExpr| None) => `(Expr.value <| Value.none)
  | `(nkiExpr| True) => `(Expr.value <| Value.bool true)
  | `(nkiExpr| False) => `(Expr.value <| Value.bool false)
  | `(nkiExpr| $n:num) => `(Expr.value <| Value.int $n)
  | `(nkiExpr| $n:scientific) => `(Expr.value <| Value.float $n)
  | `(nkiExpr| $f:nkiExpr $[[$[$typArgs],*]]? ($[$args],*)) => mkNKIApp f (typArgs.getD #[]) args
  | `(nkiExpr| $thn:nkiExpr if $flag:nkiExpr else $els:nkiExpr) => do
    let flag ← expandNKIExpr flag
    let thn ← expandNKIExpr thn
    let els ← expandNKIExpr els
    `(Expr.ifExp $flag $thn $els)
  | `(nkiExpr| range) => `(Expr.builtin Builtin.range)
  | `(nkiExpr| $e1:nkiExpr and $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.land)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr or $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.lor)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr == $e2:nkiExpr) => do
    let f ← `(Expr.typApp (Expr.builtin Builtin.eq) _ (by solve_subst))
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr != $e2:nkiExpr) => do
    let f ← `(Expr.typApp (Expr.builtin Builtin.ne) _ (by solve_subst))
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr < $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.lt)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr <= $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.le)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr > $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.gt)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr >= $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.ge)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr + $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.add)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr - $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.sub)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr * $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.mul)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr / $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.div)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr // $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.floor)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr % $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.mod)
    mkNKIApp2 f e1 e2
  | `(nkiExpr| $e1:nkiExpr ** $e2:nkiExpr) => do
    let f ← `(Expr.builtin Builtin.pow)
    mkNKIApp2 f e1 e2
  | _ => throwUnsupportedSyntax

end

def expandNKIParams (args : Array (TSyntax `nkiParam)) : NKIElabM (Array (Ident × Option (TSyntax `term))) :=
  args.mapM (fun arg =>
    match arg with
    | `(nkiParam| $i:ident) => return (i, .none)
    | `(nkiParam| _) => return (mkIdent `_, .none)
    | `(nkiParam| $i:ident : $t:nkiType) => return (i, some <| ← expandNKIType t)
    | `(nkiParam| _ : $t:nkiType) => return (mkIdent `_, some <| ← expandNKIType t)
    | _ => throwUnsupportedSyntax
  )

def getNKIFunctionSig
  (typArgs : (Array (TSyntax `ident)))
  (args : Array (TSyntax `nkiParam))
  (returns : Option (TSyntax `nkiType))
  : NKIElabM (Option (TSyntax `term)) := do
  let some returns := returns | return .none
  let returns ← expandNKIType returns
  let args ← expandNKIParams args
  let some (argTyps : Array (TSyntax `term)) :=
    args.mapM Prod.snd | return .none
  let sig ←
    typArgs.foldrM (fun t body => `(Typ.all fun $t => $body)) <|
    ← argTyps.foldrM (fun t body => `(Typ.arrow $t $body)) returns
  pure sig

def expandNKIFunctionSig : TSyntax `nkiDef → NKIElabM (Option (TSyntax `term))
  | `(nkiDef| def $_name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $_body) =>
    getNKIFunctionSig (typArgs.getD #[]) args returns
  | _ => throwUnsupportedSyntax

mutual

partial def expandNKIFunction
  (name : TSyntax `ident)
  (typArgs : Option (Array (TSyntax `ident)))
  (params : Array (TSyntax `nkiParam))
  (returns : Option (TSyntax `nkiType))
  (body : TSyntax `nkiStmtSeq)
  : NKIElabM (TSyntax `term) := do
  let paramsTerm ← expandNKIParams params
  let returnsTerm ← returns.mapM expandNKIType
  let (body, recs) ← NKIElabM.withFunc name paramsTerm do
    expandNKIStmtSeqNonEmpty body
  let body ← match returnsTerm with
    | .some t => `(Stmt.typed $t $body)
    | .none => pure body
  let funBody ←
    paramsTerm.foldrM (fun (i, t) body =>
      match t with
      | .some t => `(Stmt.abs (α := $t) (fun $i => $body))
      | .none => `(Stmt.abs (fun $i => $body))
    ) body
  let funBody ←
    match typArgs with
    | .some typArgs =>
      -- gather all parameter and return types.
      -- TODO: Add type inference support here
      let argTyps ←
        paramsTerm.mapM (fun (argName, t) =>
          match t with
          | .some t => pure t
          | .none => throwErrorAt argName "cannot infer argument types for generic function"
        )
      let returnsTerm ←
        (match returnsTerm with
         | .some t => pure t
         | .none => throwErrorAt name "cannot infer return type for generic function")
      -- construct the monotype
      let sig ← argTyps.foldrM (fun t returns => `(Typ.arrow $t $returns)) returnsTerm
      -- here we need to simultaneously construct the polytype and the term
      let (_, funBody) ← typArgs.foldrM (fun tArg (sig, body) => do
        -- extend the signature with a Lean lambda abstraction
        -- if the signature we have right now is another Lean abstraction,
        -- we need to first wrap it in a call to `Typ.all`
        -- to understand why this is, take a look how `Typ.all` and `Stmt.typAbs` are defined
        let sig ←
          (match sig with
           | `(fun $a => $b) => `(fun $tArg => Typ.all fun $a => $b)
           | _ => `(fun $tArg => $sig))
        -- extend the term with a type abstraction
        let body ← `(Stmt.typAbs $sig (fun $tArg => $body))
        pure (sig, body)
      ) (sig, funBody)
      pure funBody
    | .none => pure funBody
  let funBody ←
    match ← getNKIFunctionSig (typArgs.getD #[]) params returns with
    | .some sig => `(Stmt.typed $sig $funBody)
    | .none => pure funBody
  if recs then
    `(Def.recur (fun $name => $funBody))
  else
    `(Def.stmts $funBody)

partial def expandNKIDef : TSyntax `nkiDef → NKIElabM (TSyntax `ident × TSyntax `term)
  | `(nkiDef| def $name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $body) => do
    return (name, ← expandNKIFunction name typArgs args returns body)
  | _ => throwUnsupportedSyntax

partial def expandNKILet
  (name : Ident)
  (rhs : TSyntax `term)
  (typ : Option (TSyntax `term))
  (isDef : Bool)
  (c : List (TSyntax `nkiStmt))
  : NKIElabM (TSyntax `term) := do
  NKIElabM.pushBVar name
  let body ←
    -- if the continutation is empty, append a `return None` for type-checking purposes
    match c with
    | [] =>
      if ← NKIElabM.atTopLevel then
        `(fun _ => Stmt.ret (Expr.value (Value.none)))
      else
        `(fun _ => Stmt.expr (Expr.value (Value.none)))
    | stmt' :: c => `(fun $name => $(← expandNKIStmt stmt' c))
  let ctor ← if isDef then `(Stmt.letDef) else `(Stmt.letBind)
  match typ with
  | .some typ => `($ctor (α := $typ) $rhs $body)
  | .none => `($ctor $rhs $body)

partial def expandNKIStmt (stmt : TSyntax `nkiStmt) (cont : List (TSyntax `nkiStmt)) : NKIElabM (TSyntax `term) := do
  match stmt with
  | `(nkiStmt| $name:ident $[: $typ]? = $rhs) =>
    let rhs ← expandNKIExpr rhs
    let typ ← typ.mapM expandNKIType
    expandNKILet name rhs typ false cont
  | `(nkiStmt| $dfn:nkiDef) =>
    let sig ← expandNKIFunctionSig dfn
    let (name, dfn) ← expandNKIDef dfn
    expandNKILet name dfn sig true cont
  | `(nkiStmt| $e:nkiExpr) =>
    let stmt ← `(Stmt.expr $(← expandNKIExpr e))
    expandNKIStmtCont false stmt cont
  | `(nkiStmt| return $e) =>
    let stmt ← `(Stmt.ret $(← expandNKIExpr e))
    expandNKIStmtCont true stmt cont
  | `(nkiStmt|
      if $cond:nkiExpr:
        $thn:nkiStmtSeq
    ) => do
    let stmt ← NKIElabM.withTopLevel false do
      let cond ← expandNKIExpr cond
      let thn ← expandNKIStmtSeqNonEmpty thn
      `(Stmt.ifStm $cond $thn)
    expandNKIStmtCont false stmt cont
  | `(nkiStmt|
      if $cond:nkiExpr:
        $thn:nkiStmtSeq
      else:
        $els:nkiStmtSeq
    ) => do
    let stmt ← NKIElabM.withTopLevel cont.isEmpty do
      let cond ← expandNKIExpr cond
      let thn ← expandNKIStmtSeqNonEmpty thn
      let els ← expandNKIStmtSeqNonEmpty els
      let ctor ← if cont.isEmpty then `(Stmt.ifElsStmRet) else `(Stmt.ifElsStm)
      `($ctor $cond $thn $els)
    expandNKIStmtCont true stmt cont
  | `(nkiStmt|
      for $x:ident in $iter:nkiExpr:
        $body) => do
    let stmt ← NKIElabM.withTopLevel false <| NKIElabM.withBVar x do
      let iter ← expandNKIExpr iter
      let body ← expandNKIStmtSeqNonEmpty body
      `(Stmt.forLoop $iter (fun $x => $body))
    expandNKIStmtCont false stmt cont
  | `(nkiStmt|
      while $cond:nkiExpr:
        $body) => do
    let stmt ← NKIElabM.withTopLevel false do
      let cond ← expandNKIExpr cond
      let body ← expandNKIStmtSeqNonEmpty body
      `(Stmt.whileLoop $cond $body)
    expandNKIStmtCont false stmt cont
  | _ => throwUnsupportedSyntax

partial def expandNKIStmtCont
  (returned : Bool)
  (stmt : TSyntax `term)
  (cont : List (TSyntax `nkiStmt))
  : NKIElabM (TSyntax `term) := do
  match cont with
  | [] =>
    if returned then
      pure stmt
    else
      if ← NKIElabM.atTopLevel then
        `(Stmt.seq $stmt (Stmt.ret (Expr.value Value.none)))
      else
        `(Stmt.seq $stmt (Stmt.expr (Expr.value Value.none)))
  | stmt' :: cont =>
    let cont ← expandNKIStmt stmt' cont
    `(Stmt.seq $stmt $cont)

partial def expandNKIStmtSeqNonEmpty (s : TSyntax `nkiStmtSeq) : NKIElabM (TSyntax `term) :=
  match s with
  | `(nkiStmtSeq| $[$stmts]*) => do
    match stmts.toList with
    | [] => throwErrorAt s "cannot have an empty statement here"
    | stmt :: c => expandNKIStmt stmt c
  | _ => throwUnsupportedSyntax

end

def expandNKIKernel (dfn : TSyntax `nkiDef) : TermElabM (Ident × TSyntax `term × TSyntax `term) := do
  let (sig, _) ← Term.liftNKIElabM (expandNKIFunctionSig dfn)
  let some sig := sig | throwErrorAt dfn "please annotate top-level function signature"
  let ((name, body), ctx) ← Term.liftNKIElabM (expandNKIDef dfn)
  let body ← `(Kernel.dfn $body)
  let body ← ctx.fvars.foldrM (fun (name, typ) body => `(Kernel.fvar $typ fun $name => $body)) body
  pure (name, body, sig)

open Command in
set_option hygiene false in
scoped elab dfn:nkiDef : command => do
  let (name, body, sig) ← liftTermElabM (expandNKIKernel dfn)
  let def_ ←
    `(command|
      def $name {T : Kind → Type} {V : (κ : Kind) → Typ T κ → Type} : Kernel T V $sig :=
        $body
    )
  elabCommand def_

/-!
# ---------------------------End of Macro--------------------------------------
-/

/-!
# ---------------------------Start of Delab------------------------------------
-/

scoped notation "None" => Typ.prim Prim.none
scoped notation "bool" => Typ.prim Prim.bool
scoped notation "int" => Typ.prim (Prim.numeric Numeric.int)
scoped notation "float" => Typ.prim (Prim.numeric Numeric.float)
scoped notation "string" => Typ.prim Prim.string

scoped infixr:55 " -> " => Typ.arrow

@[scoped app_unexpander Typ.var]
def unexpTypVar : PrettyPrinter.Unexpander
  | `($_tvar $i) => `($i)
  | `($_tvar) => `($_tvar)

@[scoped app_unexpander Typ.all]
def unexpTypAll : PrettyPrinter.Unexpander
  | `($_tall fun $i => $b) => `(∀ $(⟨i⟩), $b)
  | `($_tall) => `($_tall)

/-!
# ---------------------------End of Delab--------------------------------------
-/
