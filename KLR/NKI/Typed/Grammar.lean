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
Types in NKI
-/
declare_syntax_cat nkiType

scoped syntax "(" nkiType ")" : nkiType
scoped syntax ident : nkiType
scoped syntax "none" : nkiType
scoped syntax "int" : nkiType
scoped syntax "bool" : nkiType
scoped syntax "float" : nkiType
scoped syntax "string" : nkiType
scoped syntax:50 nkiType:51 " -> " nkiType:50 : nkiType

/--
NKI Expressions
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
-- TODO: tensor

-- Expr
scoped syntax ident : nkiExpr -- var

/--
if-expressions, these must fit in one line to avoid collisions with if-statements
-/
scoped syntax nkiExpr !linebreak " if " !linebreak nkiExpr !linebreak " else " !linebreak nkiExpr : nkiExpr

/--
call-expressions
-/
scoped syntax nkiExpr ("[" nkiType,* "]")? "(" nkiExpr,* ")" : nkiExpr

-- TODO: built-ins

/--
Function parameters in NKI
-/
declare_syntax_cat nkiParam

scoped syntax ident (" : " nkiType)? : nkiParam

/--
Unused function parameters
-/
scoped syntax "_" (" : " nkiType)? : nkiParam

/--
Statments in NKI
-/
declare_syntax_cat nkiStmt

/--
A seqeuqnce of NKI statements
-/
declare_syntax_cat nkiStmtSeq

@[inline] def nkiStmtParser (rbp : Nat := 0) : Parser :=
  categoryParser `nkiStmt rbp

def nkiStmtSeq1Idented := leading_parser
  sepBy1Indent nkiStmtParser "; " (allowTrailingSep := true)

scoped syntax nkiStmtSeq1Idented : nkiStmtSeq

/--
Function definitions in NKI
-/
declare_syntax_cat nkiDef

scoped syntax withPosition("def " ident ("[" ident,* "]")? "(" nkiParam,* ")" (" -> " nkiType)? ":" colGt nkiStmtSeq) : nkiDef
scoped syntax withPosition("def_rec " ident ("[" ident,* "]")? "(" nkiParam,* ")" (" -> " nkiType)? ":" colGt nkiStmtSeq) : nkiDef
scoped syntax nkiDef : nkiStmt

scoped syntax nkiExpr : nkiStmt

scoped syntax "return " nkiExpr : nkiStmt

/--
assignments/let-bindings
-/
scoped syntax ident !linebreak (" : " !linebreak nkiType)? !linebreak " = " !linebreak nkiExpr : nkiStmt

/--
if-statements
-/
scoped syntax withPosition("if " nkiExpr ":" linebreak (colGt nkiStmtSeq) (colEq "else:" linebreak colGt nkiStmtSeq)?) : nkiStmt

/--
for loops
-/
scoped syntax withPosition("for " ident " in " nkiExpr ":" linebreak colGt nkiStmtSeq) : nkiStmt

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
Free variables in a NKI def, an array of identifiers and their types
-/
abbrev NKIFVars := Array (Ident × TSyntax `term)

structure Context where
  bvars : Array Ident := #[]
  fvars : NKIFVars := #[]

abbrev NKIElabM := StateT Context Elab.TermElabM

def NKIElabM.pushBVar (v : Ident) : NKIElabM Unit := do
  let c ← get
  set {c with bvars := c.bvars.push v}

def NKIElabM.popBVar : NKIElabM Unit := do
  let c ← get
  set {c with bvars := c.bvars.pop}

def NKIElabM.addFVar (i : Ident) (typ : TSyntax `term) : NKIElabM Unit := do
  let c ← get
  if !(c.fvars.map Prod.snd).contains i then
    set {c with fvars := c.fvars.push (i, typ)}

def NKIElabM.isBound (i : Ident) : NKIElabM Bool := do
  let { bvars, .. } ← get
  return bvars.contains i

def Command.liftNKIElabM {α : Type} (x : NKIElabM α) : Command.CommandElabM (α × Context) :=
  Command.liftTermElabM <| StateT.run x {}

def nkiTypeToSyntaxAux (bvars : List Ident) : Lean.Expr → NKIElabM (TSyntax `term)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.none []) =>
    `(Typ.prim Prim.none)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.int []) =>
    `(Typ.prim Prim.int)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.bool []) =>
    `(Typ.prim Prim.bool)
  | mkApp2 (.const `KLR.NKI.Typed.Typ.prim []) _ (.const `KLR.NKI.Typed.Prim.float []) =>
    `(Typ.prim Prim.float)
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
Turn a `Lean.Expr` representing a `NKI.Typed.Typ` into a `Lean.Syntax`.
This is used for defining free variables in a NKI statement.
-/
def nkiTypeToSyntax (e : Lean.Expr) : NKIElabM (TSyntax `term) :=
  nkiTypeToSyntaxAux [] e

partial def expandNKIType : TSyntax `nkiType → NKIElabM (TSyntax `term)
  | `(nkiType| ($t:nkiType)) => expandNKIType t
  | `(nkiType| $i:ident) => `(Typ.var $i)
  | `(nkiType| none) => `(Typ.prim Prim.none)
  | `(nkiType| int) => `(Typ.prim Prim.int)
  | `(nkiType| bool) => `(Typ.prim Prim.bool)
  | `(nkiType| float) => `(Typ.prim Prim.float)
  | `(nkiType| string) => `(Typ.prim Prim.float)
  | `(nkiType| $t1:nkiType -> $t2:nkiType) => do
    let t1 ← expandNKIType t1
    let t2 ← expandNKIType t2
    `(Typ.arrow $t1 $t2)
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
  -- TODO: a specialized tactic here with better error reporting than `aesop`
  (← typArgs.foldlM (fun f arg => `(Expr.typApp $f $arg (by aesop))) f)
    |> args.foldlM (fun f arg => `(Expr.app $f $arg))

partial def expandNKIExpr : TSyntax `nkiExpr → NKIElabM (TSyntax `term)
  | `(nkiExpr| ($e:nkiExpr)) => expandNKIExpr e
  | `(nkiExpr| $i:ident) => do
    /-
    Identifiers require special support.

    If it is a currently bound variable in the NKI statement,
    nothing special needs to be done.

    If it is not, we need to see if it can be found in the Lean context,
    get its type, and record it as a free variable in `Context`.
    Then the top-level elaboration will add the appropriate `fvar` declarations
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
  let argTyps : Option (Array (TSyntax `term)) :=
    args.mapM (fun (_, t) =>
      match t with
      | .some t => t
      | .none => .none
    )
  let some argTyps := argTyps | return .none
  let sig ←
    typArgs.foldrM (fun t body => `(Typ.all fun $t => $body))
    <| ← argTyps.foldrM (fun t body => `(Typ.arrow $t $body)) returns
  pure sig

def expandNKIFunctionSig : TSyntax `nkiDef → NKIElabM (Option (TSyntax `term))
  | `(nkiDef| def $_name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $_body) =>
    getNKIFunctionSig (typArgs.getD #[]) args returns
  | `(nkiDef| def_rec $_name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $_body) =>
    getNKIFunctionSig (typArgs.getD #[]) args returns
  | _ => throwUnsupportedSyntax

mutual

partial def expandNKIFunction
  (rec_ : Bool)
  (name : TSyntax `ident)
  (typArgs : Option (Array (TSyntax `ident)))
  (params : Array (TSyntax `nkiParam))
  (returns : Option (TSyntax `nkiType))
  (body : TSyntax `nkiStmtSeq)
  : NKIElabM (TSyntax `term) := do
  let paramsTerm ← expandNKIParams params
  let returnsTerm ← returns.mapM expandNKIType

  -- Add bound variables
  if rec_ then
    NKIElabM.pushBVar name
  paramsTerm.forM (fun (name, _) => NKIElabM.pushBVar name)

  -- expand the body
  let body ← expandNKIStmtSeq body

  -- Remove bound variables
  if rec_ then
    NKIElabM.popBVar
  paramsTerm.forM (fun _ => NKIElabM.popBVar)

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
      -- TODO: Support type inference here
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
  if rec_ then
    match ← getNKIFunctionSig (typArgs.getD #[]) params returns with
    | .some sig => `(Stmt.rec_ (α := $sig) (fun $name => $funBody))
    | .none => `(Stmt.rec_ (fun $name => $funBody))
  else
    pure funBody

partial def expandNKIDef : TSyntax `nkiDef → NKIElabM (TSyntax `ident × TSyntax `term)
  | `(nkiDef| def $name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $body) => do
    return (name, ← expandNKIFunction false name typArgs args returns body)
  | `(nkiDef| def_rec $name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $body) => do
    return (name, ← expandNKIFunction true name typArgs args returns body)
  | _ => throwUnsupportedSyntax

partial def expandNKIStmt (stmt : TSyntax `nkiStmt) (c : List (TSyntax `nkiStmt)) : NKIElabM (TSyntax `term) := do
  let stmt ←
    match stmt with
    | `(nkiStmt| $name:ident $[: $typ]? = $rhs) => do
      -- if the continutation is empty, append a `return None` for type-checking purposes
      let typ ← typ.mapM expandNKIType
      let rhs ← expandNKIExpr rhs
      NKIElabM.pushBVar name
      let body ←
        match c with
        | [] => `(fun _ => Stmt.ret (Expr.value (Value.none)))
        | stmt' :: c => `(fun $name => $(← expandNKIStmt stmt' c))
      let res ←
        match typ with
        | .some typ => `(Stmt.let_ (α := $typ) $rhs $body)
        | .none => `(Stmt.let_ $rhs $body)
      -- IMPORTANT: let statement elaborations short-circuit with a return!
      -- this is because of the special consideration for the continutation
      return res
    | `(nkiStmt| $d:nkiDef) => do
      let sig ← expandNKIFunctionSig d
      let (name, d) ← expandNKIDef d
      -- rewrite this into a let-binding
      NKIElabM.pushBVar name
      let body ←
        match c with
        | [] => `(fun _ => Stmt.ret (Expr.value Value.none))
        | stmt' :: c => `(fun $name => $(← expandNKIStmt stmt' c))
      let res ←
        match sig with
        | some sig => `(Stmt.let_def (α := $sig) $d $body)
        | .none => `(Stmt.let_def $d $body)
      -- IMPORTANT: short-circuit here also
      return res
    | `(nkiStmt| $e:nkiExpr) => do `(Stmt.expr $(← expandNKIExpr e))
    | `(nkiStmt| return $e) => do `(Stmt.ret $(← expandNKIExpr e))
    | `(nkiStmt|
        if $cond:nkiExpr:
          $thn:nkiStmtSeq
      ) => do
      let cond ← expandNKIExpr cond
      let thn ← expandNKIStmtSeq thn
      `(Stmt.ifStm $cond $thn)
    | `(nkiStmt|
        if $cond:nkiExpr:
          $thn:nkiStmtSeq
        else:
          $els:nkiStmtSeq
      ) => do
      let cond ← expandNKIExpr cond
      let thn ← expandNKIStmtSeq thn
      let els ← expandNKIStmtSeq els
      `(Stmt.ifElsStm $cond $thn $els)
    | _ => throwUnsupportedSyntax
  match c with
  | [] => pure stmt
  | stmt' :: c =>
    let c ← expandNKIStmt stmt' c
    `(Stmt.seq $stmt $c)

partial def expandNKIStmtSeq (s : TSyntax `nkiStmtSeq) : NKIElabM (TSyntax `term) :=
  match s with
  | `(nkiStmtSeq| $[$stmts]*) => do
    match stmts.toList with
    | [] => throwErrorAt s "cannot have an empty statement here"
    | stmt :: c => expandNKIStmt stmt c
  | _ => throwUnsupportedSyntax

end

open Command in
set_option hygiene false in
scoped elab d:nkiDef : command => do
  let (sig, _) ← liftNKIElabM (expandNKIFunctionSig d)
  let some sig := sig | throwErrorAt d "please annotate top-level function signature"
  let ((name, body), ctx) ← liftNKIElabM (expandNKIDef d)
  let body ← ctx.fvars.foldrM (fun (name, typ) body => `(Stmt.fvar $typ fun $name => $body)) body
  let def_ ←
    `(command|
      def $name {T : Kind → Type} {V : (κ : Kind) → Typ T κ → Type} : Kernel T V $sig :=
        Stmt.def_ $body
    )
  elabCommand def_

/-!
# ---------------------------End of Macro--------------------------------------
-/

/-!
# ---------------------------Start of Delab------------------------------------
-/

scoped notation "none" => Typ.prim Prim.none
scoped notation "bool" => Typ.prim Prim.bool
scoped notation "int" => Typ.prim Prim.int
scoped notation "float" => Typ.prim Prim.float
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

@[scoped app_unexpander Stmt]
def unexpStmt : PrettyPrinter.Unexpander
  | `($_Stmt $_ $_ $_ $t $_) => `($t)
  | `($_Stmt) => `($_Stmt)

/-!
# ---------------------------End of Delab--------------------------------------
-/
