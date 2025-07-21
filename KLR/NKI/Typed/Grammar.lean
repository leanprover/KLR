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

namespace KLR.NKI.Typed

open Lean Parser


/-!
# ---------------------------Start of Grammar------------------------------------
-/

/--
Types in NKI
-/
declare_syntax_cat nkiType

syntax ident : nkiType
syntax "none" : nkiType
syntax "int" : nkiType
syntax "bool" : nkiType
syntax "float" : nkiType
syntax "string" : nkiType
syntax:50 nkiType:51 " -> " nkiType:50 : nkiType

/--
NKI Expressions
-/
declare_syntax_cat nkiExpr

-- Values
syntax "None" : nkiExpr
syntax "True" : nkiExpr
syntax "False" : nkiExpr
syntax num : nkiExpr -- int
syntax scientific : nkiExpr -- float
syntax str : nkiExpr
-- TODO: tensor

-- Expr
syntax ident : nkiExpr -- var

/--
if-expressions, these must fit in one line to avoid collisions with if-statements
-/
syntax nkiExpr !linebreak " if " !linebreak nkiExpr !linebreak " else " !linebreak nkiExpr : nkiExpr

/--
call-expressions
-/
syntax nkiExpr noWs ("[" nkiType,* "]" noWs)? "(" nkiExpr,* ")" : nkiExpr
-- syntax term noWs ("[" nkiType,* "]" noWs)? "(" nkiExpr,* ")" : nkiExpr

-- TODO: built-ins

/--
Function parameters in NKI
-/
declare_syntax_cat nkiParam

syntax ident (" : " nkiType)? : nkiParam

/--
Unused function parameters
-/
syntax "_" (" : " nkiType)? : nkiParam

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

syntax nkiStmtSeq1Idented : nkiStmtSeq

/--
Function definitions in NKI
-/
declare_syntax_cat nkiDef

syntax withPosition("def " "rec "? ident ("[" ident,* "]")? "(" nkiParam,* ")" (" -> " nkiType)? ":" colGt nkiStmtSeq) : nkiDef

syntax nkiExpr : nkiStmt
syntax "return " nkiExpr : nkiStmt
syntax ident !linebreak (" : " !linebreak nkiType)? !linebreak " = " !linebreak nkiExpr : nkiStmt
syntax withPosition("if " nkiExpr ":" linebreak (colGt nkiStmtSeq) (colEq "else:" linebreak colGt nkiStmtSeq)?) : nkiStmt
syntax withPosition("for " ident " in " nkiExpr ":" linebreak colGt nkiStmtSeq) : nkiStmt
syntax "break" : nkiStmt
syntax "continue" : nkiStmt

/-!
# ---------------------------End of Grammar------------------------------------
-/

/-!
# ---------------------------Start of Macro------------------------------------
-/

open Lean Macro Meta

partial def expandNKIType : TSyntax `nkiType → MacroM (TSyntax `term)
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
  | _ => throwUnsupported

mutual

partial def mkNKIApp (f : TSyntax `nkiExpr) (typArgs : Array (TSyntax `nkiType)) (args : Array (TSyntax `nkiExpr)) : MacroM (TSyntax `term) := do
  let f ← expandNKIExpr f
  let typArgs ← typArgs.mapM expandNKIType
  let args ← args.mapM expandNKIExpr
  -- TODO: a specialized tactic here with better error reporting than `aesop`
  (← typArgs.foldlM (fun f arg => `(Expr.typApp $f $arg (by aesop))) f)
    |> args.foldlM (fun f arg => `(Expr.app $f $arg))

partial def expandNKIExpr : TSyntax `nkiExpr → MacroM (TSyntax `term)
  | `(nkiExpr| $i:ident) => `(Expr.var $i)
  | `(nkiExpr| True) => `(Expr.value <| Value.bool true)
  | `(nkiExpr| False) => `(Expr.value <| Value.bool false)
  | `(nkiExpr| $n:num) => `(Expr.value <| Value.int $n)
  | `(nkiExpr| $n:scientific) => `(Expr.value <| Value.float $n)
  -- | `(nkiExpr| $f:nkiExpr($[$args],*)) => mkNKIApp (.inl f) #[] args
  | `(nkiExpr| $f:nkiExpr$[[$[$typArgs],*]]?($[$args],*)) => mkNKIApp f (typArgs.getD #[]) args
  -- | `(nkiExpr| $f:term($[$args],*)) => mkNKIApp (.inr f) #[] args
  -- | `(nkiExpr| $f:term$[[$[$typArgs],*]]?($[$args],*)) => mkNKIApp (.inr f) (typArgs.getD #[]) args
  | `(nkiExpr| $thn:nkiExpr if $flag:nkiExpr else $els:nkiExpr) => do
    let flag ← expandNKIExpr flag
    let thn ← expandNKIExpr thn
    let els ← expandNKIExpr els
    `(Expr.ifExp $flag $thn $els)
  | _ => throwUnsupported

end

def expandNKIParams (args : Array (TSyntax `nkiParam)) : MacroM (Array (Ident × Option (TSyntax `term))) :=
  args.mapM (fun arg =>
    match arg with
    | `(nkiParam| $i:ident) => return (i, .none)
    | `(nkiParam| _) => return (mkIdent `_, .none)
    | `(nkiParam| $i:ident : $t:nkiType) => return (i, some <| ← expandNKIType t)
    | `(nkiParam| _ : $t:nkiType) => return (mkIdent `_, some <| ← expandNKIType t)
    | _ => throwUnsupported
  )

def getNKIFunctionSig (typArgs : Option (Array (TSyntax `ident)))
  (args : Array (TSyntax `nkiParam)) (returns : Option (TSyntax `nkiType))
  : MacroM (Option (TSyntax `term)) := do
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
  let sig ← argTyps.foldrM (fun t body => `(Typ.arrow $t $body)) returns
  match typArgs with
  | .some typArgs =>
    let sig ← typArgs.foldrM (fun t body => `(Typ.all fun $t => $body)) sig
    pure sig
  | .none => pure sig

def expandNKIFunctionSig : TSyntax `nkiDef → MacroM (Option <| TSyntax `term)
  | `(nkiDef| def $[rec]? $_name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $_body) =>
    getNKIFunctionSig typArgs args returns
  | _ => throwUnsupported

-- partial def getNKIDefName : TSyntax `nkiDef → MacroM Ident
--   | `(nkiDef| def $[rec]? $name $[[ $[$_],* ]]? ( $[ $_ ],* ) $[-> $_]? : $_) => pure name
--   | _ => throwUnsupported

mutual

partial def expandNKIFunction (rec_ : Bool) (name : TSyntax `ident)
  (typArgs : Option (Array (TSyntax `ident)))
  (params : Array (TSyntax `nkiParam))
  (returns : Option (TSyntax `nkiType))
  (body : TSyntax `nkiStmtSeq)
  : MacroM (TSyntax `term) := do
  let paramsTerm ← expandNKIParams params
  let returnsTerm ← returns.mapM (fun t => expandNKIType t)
  let body ← expandNKIStmtSeq body
  let body ← match returnsTerm with
    | .some t => `(Stmt.typed $t $body)
    | .none => pure body
  let funBody ← paramsTerm.foldrM (fun (i, t) body =>
    match t with
    | .some t => `(Stmt.abs (α := $t) (fun $i => $body))
    | .none => `(Stmt.abs (fun $i => $body))
  ) body
  let funBody ←
    match typArgs with
    | .some typArgs =>
      let returnsTerm ←
        (match returnsTerm with
         | .some t => pure t
         | .none => Macro.throwErrorAt name "cannot infer return type for generic function")
      let argTyps ← paramsTerm.mapM (fun (argName, t) =>
        match t with
        | .some t => pure t
        | .none => Macro.throwErrorAt argName "cannot infer argument types for generic function"
      )
      let sig ← argTyps.foldrM (fun t returns => `(Typ.arrow $t $returns)) returnsTerm
      let (_, funBody) ← typArgs.foldrM (fun tArg (sig, body) => do
        let sig ←
          (match sig with
          | `(fun $a => $b) => `(fun $tArg => Typ.all fun $a => $b)
          | _ => `(fun $tArg => $sig))
        let body ← `(Stmt.typAbs $sig (fun $tArg => $body))
        return (sig, body)
      ) (sig, funBody)
      pure funBody
    | .none => pure funBody
  let funBody ←
    match params with
    | #[] => `(Stmt.nullaryAbs $funBody)
    | _ => pure funBody
  if rec_ then
    match ← getNKIFunctionSig typArgs params returns with
    | .some sig => `(Stmt.rec_ (α := $sig) (fun $name => $funBody))
    | .none => `(Stmt.rec_ (fun $name => $funBody))
  else
    return funBody

partial def expandNKIDef : TSyntax `nkiDef → MacroM (TSyntax `ident × TSyntax `term)
  | `(nkiDef| def $name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $body) => do
    return (name, ← expandNKIFunction false name typArgs args returns body)
  | `(nkiDef| def rec $name $[[ $[$typArgs],* ]]? ( $[ $args ],* ) $[-> $returns]? : $body) => do
    return (name, ← expandNKIFunction true name typArgs args returns body)
  | _ => throwUnsupported

partial def expandNKIStmt (stmt : TSyntax `nkiStmt) (c : List (TSyntax `nkiStmt)) : MacroM (TSyntax `term) := do
  let stmt ←
    match stmt with
    | `(nkiStmt| $name:ident $[: $typ]? = $rhs) => do
      match c with
      | [] =>
        -- TODO: this should probably be a warning, but we do not have a notion of nop statements
        Macro.throwErrorAt stmt "let bindings at the end of a block is ignored"
      | stmt' :: c =>
        let typ ← typ.mapM expandNKIType
        let rhs ← expandNKIExpr rhs
        let body ← `(fun $name => $(← expandNKIStmt stmt' c))
        match typ with
        | .some typ => `(Stmt.let_ (α := $typ) $rhs $body)
        | .none => `(Stmt.let_ $rhs $body)
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
    | _ => throwUnsupported
  match c with
  | [] => pure stmt
  | stmt' :: c =>
    let c ← expandNKIStmt stmt' c
    `(Stmt.seq $stmt $c)

partial def expandNKIStmtSeq (s : TSyntax `nkiStmtSeq) : MacroM (TSyntax `term) :=
  match s with
  | `(nkiStmtSeq| $[$stmts]*) => do
    match stmts.toList with
    | [] => Macro.throwErrorAt s "cannot have an empty statement here"
    | stmt :: c => expandNKIStmt stmt c
  | _ => throwUnsupported

end

def expandNKIDefs (ds : List (TSyntax `nkiDef)) : MacroM (TSyntax `term) := do
  match ds with
  | [] => Macro.throwError "empty NKI def"
  | [d] =>
    let (_, d) ← expandNKIDef d
    `(Stmt.def_ $d)
  | d :: ds =>
    let (name, d) ← expandNKIDef d
    let body ← `(fun $name => $(← expandNKIDefs ds))
    `(Stmt.def_cont $d $body)

syntax "nki<" nkiDef* ">" : term
macro_rules
| `(nki< $[$ds]* >) => expandNKIDefs ds.toList

  -- let (name, body) ← expandNKIDef d
  -- let some sig ← expandNKIFunctionSig d
  --   | Macro.throwErrorAt d "type infererence not currently supported for top-level function signatures"
  -- `(
  --   def $name
  --     {$(mkIdent `T) : Kind → Type}
  --     {$(mkIdent `V) : ($(mkIdent `κ) : Kind) → Typ $(mkIdent `T) $(mkIdent `κ) → Type}
  --     : Kernel $(mkIdent `T) $(mkIdent `V) $sig :=
  --     $body
  -- )

/-!
# ---------------------------End of Macro--------------------------------------
-/

/-!
# ---------------------------Start of Delab------------------------------------
-/

scoped notation "None" => Typ.prim Prim.none
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

namespace Examples

def kernel {T V} : Kernel T V (int -> int) := nki<

def foo(b : bool) -> bool:
  b = False if b else True
  if b:
    return False
  return True

def bar(b):
  b = False if b else True;
  if b:
    return True
  else:
    return foo(b)

/-
TODO: automatic `rec` analysis
-/
def rec explode() -> int:
  return explode()

def higher(f : int -> int) -> int:
  return f(0)

def id_int(a):
  return a

def call_higher() -> int:
  return higher(id_int)

def higher_poly[A](f : A -> A, a : A) -> A:
  return f(a)

def call_higher_poly() -> int:
  return higher_poly[int](id_int, 0)

/-
SKI Combinators
-/

def I[A](a : A) -> A:
  return a

def K[A, B](a : A, b : B) -> A:
  return a

def S[A, B](x : A -> B -> B, y : A -> B, z : A) -> B:
  return x(z, y(z))

/-
Limitation: cannot infer polymorphic function types

def p(a):
  return a
-/

/-
The last function is the type of this entire block
-/
def ker(a: int) -> int:
  return a

>

/-
TODO: Bug

def kernel3 {T V} : Kernel T V (int -> int) := nki<

def foo(a : int) -> int:
  b = a
  return b

>
-/

/--
TODO: Why does this work? The declared type is not polymorphic!
-/
def kernel1 {T V} : Kernel T V (int -> int) := nki<

def bar[A](a : A) -> A:
  return a

>

/--
TODO: This should definitely not work!
-/
def kernel2 {T V} : Kernel T V (.all fun a => .var a -> .var a) := nki<

def foo(a : int) -> int:
  return a

>
