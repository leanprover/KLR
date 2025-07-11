/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import KLR.NKI.Simplify
import KLR.NKI.Types
import KLR.Compile.Pass

/-!
# Typed IR for NKI

This includes the following simplications
- Tuples are removed
- Function calls are curried and no default or keyword args are allowed
- Binnary ops become calls of constant functions
- `Stmt`s have `seq` which removed the need for `List Stmt`
- Introduce let bindings in `Stmt`
- No un-initialized variables allowed
-/

namespace KLR.NKI

namespace TIR

inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | tensor (shape : List Nat) (dtype : Core.Dtype) --(value : TensorLib.Tensor)

/--
TODO: Manage overloading better?
-/
inductive Const where
  -- logical
  | land | lor
  -- bitwise
  | lshift | rshift | or | xor | and
  -- comparison
  | eq | ne
  | lt_int_int | lt_int_float | lt_float_int | lt_float_float
  | le_int_int | le_int_float | le_float_int | le_float_float
  | gt_int_int | gt_int_float | gt_float_int | gt_float_float
  | ge_int_int | ge_int_float | ge_float_int | ge_float_float
  -- arithmetic
  | add_int_int | add_int_float | add_float_int | add_float_float
  | sub_int_int | sub_int_float | sub_float_int | sub_float_float
  | mul_int_int | mul_int_float | mul_float_int | mul_float_float
  | div_int_int | div_int_float | div_float_int | div_float_float
  | mod_int_int | mod_int_float | mod_float_int | mod_float_float
  | pow_int_int  | pow_int_float | pow_float_int | pow_float_float
  | floor_int_int | floor_int_float | floor_float_int | floor_float_float

mutual

inductive Index where
  | coord (i : Expr)
  | slice (l u step : Option Expr)
  | ellipsis

structure Expr where
  expr : Expr'
  pos : Pos

inductive Expr' where
  | const (const : Const)
  | value (value : Value)
  | var (name : String)
  | access (expr : Expr) (indices : List Index)
  | ifExp (test body orelse : Expr)
  | app (f : Expr) (arg : Expr)
  | typApp (f : Expr) (arg : Types.Typ)

end

mutual

structure Stmt where
  stmt : Stmt'
  pos : Pos

inductive Stmt' where
  | expr (e : Expr)
  | ret (e : Expr)
  | let_ (var : String) (ty : Types.Typ) (rhs : Expr) (body : Stmt)
  | ifStm (e : Expr) (thn els : Stmt)
  | forLoop (x : String) (iter : Expr) (body : Stmt)
  | breakLoop
  | continueLoop
  | seq (s1 s2 : Stmt)

end

structure Fun where
  name : String
  file : String
  line : Nat
  body : Stmt
  typArgs : List Types.Kind
  argNames : List String
  argTyps : List Types.Typ
  retTyp : Types.Typ

structure Arg where
  name : String
  value : Expr
  typ : Types.Typ

structure Kernel where
  entry : String
  typArgs : List Types.Typ
  args : List Expr
  funs : List Fun
  globals : List Arg

def mkKernelApp (entry : String) (typArgs : List Types.Typ) (args : List Expr) : Expr :=
  let pos : Pos := ⟨0, 0, none, none⟩ -- TODO: what pos to use here?
  let typApp := typArgs.foldl (fun res typ => ⟨.typApp res typ, pos⟩) ⟨.var entry, pos⟩
  args.foldl (fun res arg => ⟨.app res arg, pos⟩) typApp

/-!
# Typing Rules
-/
open Types Compile.Pass

def Fun.sig (f : Fun) : Typ :=
  f.typArgs.foldr (fun κ typ => Π κ ⇒ typ)
  <| f.argTyps.foldr (fun argTyp retTyp => argTyp ⟶ retTyp) f.retTyp

structure Ctx where
  typs : TypCtx
  vars : List (String × Typ)
  retTyp : Option Typ

def Ctx.empty : Ctx :=
  ⟨[], [], none⟩

/--
  Set the type of the variable with `name` to be `typ`
-/
def Ctx.updateVar (Γ : Ctx) (name : String) (typ : Typ) : Ctx :=
  let vars := (name, typ) :: Γ.vars.filter (·.1 == name)
  {Γ with vars := vars}

def Ctx.updateVars (Γ : Ctx) (vars : List (String × Typ)) : Ctx :=
  vars.foldl (fun Γ (name, typ) => Γ.updateVar name typ) Γ

def Ctx.addTyp (Γ : Ctx) (κ : Kind) : Ctx :=
  {Γ with typs := Γ.typs,, κ}

def Ctx.setRet (Γ : Ctx) (ret : Typ) : Ctx :=
  {Γ with retTyp := some ret}

def Ctx.kernelInit (globals : List Arg) (funs : List Fun) : Ctx :=
  let globals := globals.map fun arg => (arg.name, arg.typ)
  let funVars := funs.map fun f => (f.name, f.sig)
  Ctx.empty.updateVars (globals ++ funVars)

def Ctx.addTyps (Γ : Ctx) (κs : List Kind) : Ctx :=
  {Γ with typs := Γ.typs ++ κs}

def Ctx.enterFun (Γ : Ctx) (typArgs : List Kind) (argNames : List String) (argTyps : List Typ) (retTyp : Typ) : Ctx :=
  ((Γ.addTyps typArgs).updateVars (argNames.zip argTyps)).setRet retTyp

def Ctx.addFun (Γ : Ctx) (f : Fun) : Ctx :=
  Γ.updateVar f.name f.sig

def Ctx.addFuns (Γ : Ctx) (funs : List Fun) : Ctx :=
  funs.foldl (fun Γ f => Γ.addFun f) Γ

/-!
# Type checking functions
-/

def Value.typ : Value → Typ
  | .none => .prim .none
  | .bool _ => .prim .bool
  | .int _ => .prim .int
  | .float _ => .prim .float
  | .string _ => .prim .string
  | .tensor shape dtype => .tensor (.shape <| shape.map .size) dtype

def Const.typ : Const → Typ
  -- logical
  | .land => .prim .bool ⟶ .prim .bool ⟶ .prim .bool
  | .lor => .prim .bool ⟶ .prim .bool ⟶ .prim .bool
  -- bitwise
  | .lshift => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .rshift => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .or => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .xor => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .and => .prim .int ⟶ .prim .int ⟶ .prim .int
  -- comparison
  | .eq => Π ⋆ ⇒ .var 0 ⟶ .var 0 ⟶ .prim .bool
  | .ne => Π ⋆ ⇒ .var 0 ⟶ .var 0 ⟶ .prim .bool
  | .lt_int_int => .prim .int ⟶ .prim .int ⟶ .prim .bool
  | .lt_int_float => .prim .int ⟶ .prim .float ⟶ .prim .bool
  | .lt_float_int => .prim .float ⟶ .prim .int ⟶ .prim .bool
  | .lt_float_float => .prim .float ⟶ .prim .float ⟶ .prim .bool
  | .le_int_int => .prim .int ⟶ .prim .int ⟶ .prim .bool
  | .le_int_float => .prim .int ⟶ .prim .float ⟶ .prim .bool
  | .le_float_int => .prim .float ⟶ .prim .int ⟶ .prim .bool
  | .le_float_float => .prim .float ⟶ .prim .float ⟶ .prim .bool
  | .gt_int_int => .prim .int ⟶ .prim .int ⟶ .prim .bool
  | .gt_int_float => .prim .int ⟶ .prim .float ⟶ .prim .bool
  | .gt_float_int => .prim .float ⟶ .prim .int ⟶ .prim .bool
  | .gt_float_float => .prim .float ⟶ .prim .float ⟶ .prim .bool
  | .ge_int_int => .prim .int ⟶ .prim .int ⟶ .prim .bool
  | .ge_int_float => .prim .int ⟶ .prim .float ⟶ .prim .bool
  | .ge_float_int => .prim .float ⟶ .prim .int ⟶ .prim .bool
  | .ge_float_float => .prim .float ⟶ .prim .float ⟶ .prim .bool
  -- arithmetic
  | .add_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .add_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .add_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .add_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float
  | .sub_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .sub_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .sub_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .sub_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float
  | .mul_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .mul_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .mul_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .mul_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float
  | .div_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .div_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .div_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .div_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float
  | .mod_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .mod_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .mod_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .mod_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float
  | .pow_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .pow_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .pow_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .pow_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float
  | .floor_int_int => .prim .int ⟶ .prim .int ⟶ .prim .int
  | .floor_int_float => .prim .int ⟶ .prim .float ⟶ .prim .float
  | .floor_float_int => .prim .float ⟶ .prim .int ⟶ .prim .float
  | .floor_float_float => .prim .float ⟶ .prim .float ⟶ .prim .float

inductive IndexKind
  | coord
  | slice
  | ellipsis

mutual

def Option.hasIntTyp (Γ : Ctx) : Option Expr → PosM Unit
  | some e => do
    let .prim .int ← e.typ Γ | throw "expected type int"
  | none => none

def Index.kind (Γ : Ctx) : Index → PosM IndexKind
  | .coord i => do
    let .prim .int ← i.typ Γ | throw "tensor index must be of type int"
    return .coord
  | .slice l u step => do
    let _ ← Option.hasIntTyp Γ l
    let _ ← Option.hasIntTyp Γ u
    let _ ← Option.hasIntTyp Γ step
    return .slice
  | .ellipsis => return .ellipsis

def Index.accessTyp (Γ : Ctx) (shape : Typ) (dtype : Core.Dtype) (indices : List IndexKind) : TypCheck := do
  match (← shape.reduceShape Γ.typs), indices with
  | .shape [_], [.coord] =>
    return .prim (.dtype dtype)
  | .shape (_::tl), [.coord] =>
    return .tensor (.shape tl) dtype
  | .shape (_::tl), .coord :: idxTl =>
    Index.accessTyp Γ (.shape tl) dtype idxTl
  | _, _ =>
    throw "unsupported access pattern"

def Expr.typ (Γ : Ctx) : Expr → TypCheck
  | {expr, pos} => withPos pos do expr.typ Γ

def Expr'.typ (Γ : Ctx) : Expr' → TypCheck
  | .const const => return const.typ
  | .value value => return value.typ
  | .var name => do
    let some (_, typ) := Γ.vars.find? (·.1 == name)
      | throw s!"\"{name}\" not found in type context"
    return typ
  | .access expr indices => do
    let .tensor shape dtype ← expr.typ Γ
      | throw "only tensor access is currently supported"
    let indices ← indices.mapM (Index.kind Γ)
    Index.accessTyp Γ shape dtype indices
  | .ifExp test body orelse => do
    let .prim .bool ← test.typ Γ
      | throw "condition of an if-expression must have type bool"
    let tBody ← body.typ Γ
    let tOrelse ← orelse.typ Γ
    if tBody ≈ tOrelse then
      return tBody
    else
      throw "both branches of an if-expression must have the same type"
  | .app f arg => do
    let dom ⟶ ran ← f.typ Γ
      | throw "only functions can be applied"
    let argTyp ← arg.typ Γ
    if dom ≈ argTyp then -- TODO: subtyping
      return ran
    else
      throw "argument type mismatch"
  | .typApp f arg => do
    let Π κ ⇒ t ← f.typ Γ
      | throw "invalid polymorphic instantiation"
    if Γ.typs ⊢⋆ arg : κ then
      return t[0 := arg]
    else
      throw "argument kind mismatch"

end

mutual

def Stmt.typ (Γ : Ctx) : Stmt → TypCheck
  | { stmt, pos } => withPos pos do stmt.typ Γ

def Stmt'.typ (Γ : Ctx) : Stmt' → TypCheck
  | .expr e => e.typ Γ
  | .ret e => do
    let t ← e.typ Γ
    let some expected := Γ.retTyp
      | throw "return outside of a a function"
    if t ≈ expected then -- TODO: subtyping
      return expected
    else
      throw "return type mismatch"
  | .let_ var ty rhs body => do
    let t ← rhs.typ Γ
    if t ≈ ty then -- TODO: subtyping
      body.typ (Γ.updateVar var ty)
    else
      throw "type mismatch"
  | .ifStm e thn els => do
    let .prim .bool ← e.typ Γ
      | throw "condition of if statement must be bool"
    let _ ← thn.typ Γ
    let _ ← els.typ Γ
    return .prim .none
  | .forLoop _ _ _ =>
    -- TODO
    throw "forLoop not currently supported"
  | .breakLoop => return .prim .none
  | .continueLoop => return .prim .none
  | .seq s1 s2 => do
    let _ ← s1.typ Γ
    s2.typ Γ

end

def Fun.typ (Γ : Ctx) (f : Fun) : TypCheck := do
  let ret ← f.body.typ (Γ.enterFun f.typArgs f.argNames f.argTyps f.retTyp)
  if ret ≈ f.retTyp then -- TODO: subtyping
    return f.sig
  else
    throw "function return type mismatch"

def Kernel.typ (k : Kernel) : TypCheck := do
  let _ ← List.mapM (fun arg => do
    let typ ← arg.value.typ .empty
    if typ ≈ arg.typ then -- TODO: subtyping
      return
    else
      throw "global arg type mismatch"
  ) k.globals
  let Γ := Ctx.kernelInit k.globals k.funs
  let _ ← List.mapM (Fun.typ Γ) k.funs
  (mkKernelApp k.entry k.typArgs k.args).typ Γ
