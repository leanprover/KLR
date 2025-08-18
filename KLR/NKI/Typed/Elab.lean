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

import KLR.NKI.Typed.Basic
import KLR.NKI.Typed.Context
import KLR.NKI.Typed.Types
import KLR.Py.Pretty

theorem List.ne_nil_of_not_empty {α} {l : List α} : ¬l.isEmpty = true → l ≠ [] := by
  intro; simp_all only [isEmpty_iff, ne_eq, not_false_eq_true]

namespace KLR.NKI.Typed

open Py (Ident FileInfo Span)

/-!
# Elaboration that turns python into fully-typed NKI
This implements the bidirectional typechecking algorithm described here:
https://arxiv.org/abs/1306.6032

Missing features:
- Unimplemented language features, grep for calls of `throwUnsupported`
- Semantic subtyping.
  For example, if a function expects: `∀ DT M N, tensor[DT, (M, N, M + N)]`,
  passing it `tensor[int, (10, 20, 30)]` should be allowed.
- Better handling of subtyping coercions.
  See comments in `Context.solve` and `stmt'` in the `ret` case.
- Better error reporting in general.
- Other todos marked by `TODO` comments.
-/

/-! # -----------Start: Parsing Type Annotations-------------- -/

mutual

def indexTyp : Py.Index → ElabM Typ
  | .coord t => typ t
  | _ => throwSyntax "unexpected type"

def indicesTyp : List Py.Index → ElabM (List Typ)
  | hd :: tl => return (← indexTyp hd) :: (← indicesTyp tl)
  | [] => return []

def forallBody : List Py.Index → List Ident → ElabM (List Ident × Typ)
  | [], _ => throwType "missing return type in forall"
  | [body], names => return (names, ← indexTyp body)
  | hd :: tl, names => do
    let hd ← match hd with | .coord ⟨_, .var id⟩ => pure id | _ => throwType "type parameter must be an identifier"
    let (tl, body) ← forallBody tl names
    return (hd :: tl, body)

def listTyp : List Py.Exp → ElabM (List Typ)
  | [] => return []
  | hd :: tl => return (← typ hd) :: (← listTyp tl)

def typ' (exp : Py.Exp') : ElabM Typ := do
  let span ← getSpan!
  match exp with
  | .var "None"     => return .prim span .none
  | .var "bool"     => return .prim span .bool
  | .var "int"      => return .prim span (.numeric .int)
  | .var "float"    => return .prim span (.numeric .float)
  | .var "str"      => return .prim span .string
  | .var "bfloat16" => return .prim span (.dtype .bfloat16)
  | .var "float8e3" => return .prim span (.dtype .float8e3)
  | .var "float8e4" => return .prim span (.dtype .float8e4)
  | .var "float8e5" => return .prim span (.dtype .float8e5)
  | .var "float16"  => return .prim span (.dtype .float16)
  | .var "float32"  => return .prim span (.dtype .float32)
  | .var "float32r" => return .prim span (.dtype .float32r)
  | .var "int8"     => return .prim span (.dtype .int8)
  | .var "int16"    => return .prim span (.dtype .int16)
  | .var "int64"    => return .prim span (.dtype .int64)
  | .var "int32"    => return .prim span (.dtype .int32)
  | .var "uint8"    => return .prim span (.dtype .uint8)
  | .var "uint16"   => return .prim span (.dtype .uint16)
  | .var "uint32"   => return .prim span (.dtype .uint32)
  | .var "uint64"   => return .prim span (.dtype .uint64)
  | .var α          => return .var span α
  | .value (.int n) =>
    if n < 0 then throwType "cannot have negative tensor dimensions" else
    return .size span n.toNat
  | .access ⟨_, .var "func"⟩ ts => do
    let ts ← indicesTyp ts
    if h : ts.isEmpty then throwType "must have at least a return type for functions" else
    let params := ts.take (ts.length - 1)
    let ret := ts.getLast <| List.ne_nil_of_not_empty h
    return .func span params ret
  | .access ⟨_, .var "iter"⟩ ts => do
    let ts ← indicesTyp ts
    if h : ts.length ≠ 1 then throwType "iter must bind exactly one type" else
    return .iter span ts[0]
  | .access ⟨span, .var "forall"⟩ ts => do
    let (names, body) ← forallBody ts []
    if names.isEmpty then throwType "forall must bind at least one type parameter" else
    return .forall span names body
  | .access ⟨_, .var "tensor"⟩ ts => do
    let ts ← indicesTyp ts
    if h : ts.length ≠ 2 then throwType "tensor type must specify a dtype and a shape like so 'tensor[dt, (n, m, k, ...)]'" else
    let dt := ts[0]
    let shape := ts[1]
    return .tensor span shape dt
  | .access ⟨_, .var "tuple"⟩ ts => do
    let ts ← indicesTyp ts
    if ts.isEmpty then throwType "empty tuple type not allowed" else
    return .tuple span ts
  | .access ⟨_, .var "list"⟩ ts => do
    let ts ← indicesTyp ts
    if h : ts.length ≠ 1 then throwType "wrong number of types bound to list" else
    return .list span ts[0]
  | .tuple ts => do
    let ts ← listTyp ts
    return .shape span ts
  | .binOp .add x y => do
    let x ← typ x
    let y ← typ y
    return .sizeAdd span x y
  | .binOp .matmul x y => do
    let x ← typ x
    let y ← typ y
    return .shapeAppend span x y
  | _ => throwType "invalid type"

def typ : Py.Exp → ElabM Typ
  | { span, exp } => withSpan span do typ' exp

end

/-! # -----------End: Parsing Type Annotations-------------- -/


/-! # -----------Start: Type Checking Utilities -------------- -/

partial def Context.typewf (Γ : Context) (typ : Typ) : ElabM Unit := do
  match typ with
  | .var _ name =>
    if !Γ.foralls.contains name then
      throwType s!"type variable {name} not found in context"
  | .evar _ name =>
    if !Γ.existentials.contains name then
      throwType s!"meta variable {name} not found in context"
  | .forall _ names body =>
    let c' := Γ ++ (names.map fun x => .forall x).toArray
    c'.typewf body
  | .func _ params ret =>
    (Γ.typewf ret)
    params.forM Γ.typewf
  | .prim _ _
  | .size _ _ => return
  | .shape _ dims => dims.forM Γ.typewf
  | .tuple _ typs => typs.forM Γ.typewf
  | .list _ t => Γ.typewf t
  | .tensor _ sh dt => Γ.typewf sh; Γ.typewf dt
  | .iter _ t => Γ.typewf t
  | .sizeAdd _ x y => Γ.typewf x; Γ.typewf y
  | .shapeAppend _ s1 s2 => Γ.typewf s1; Γ.typewf s2

-- partial def Context.wf (c : Context) : ElabM Unit := do
--   if h : c.size = 0 then return else
--   let ce := c[0]
--   let cs := c[1:].toArray
--   match ce with
--   | .forall name =>
--     if (Context.foralls cs).contains name then
--       throwType s!"duplicated type variable {name} in context"
--   | .var name typ =>
--     if (Context.vars cs).contains name then
--       throwType s!"duplicated variable {name} in context"
--     Context.typewf cs typ
--   | .exists name => !(Context.existentials cs).contains name
--   | .existsSolved name t =>
--     t.isMonotype
--     && !(Context.existentials cs).contains name
--     && Context.typewf cs t
--   | .marker name =>
--     !(Context.markers cs).contains name
--     && !(Context.existentials cs).contains name
--   Context.wf cs

def Context.solve (Γ : Context) (α : Ident) (t : Typ) : ElabM (Option Context) := do
  Γ.typewf t
  if !t.isMonotype then return none else
  let some (cL, cR) := Γ.breakMarker (.exists α) | {
    /-
    If the code reaches here, it means we cannot find `.exists α` in the context,
    implying that `α` is already solved since we replace `.exists α` with `.existsSolved α τ`
    when solving types.

    Normally, we would just return the existing context.
    But in our system, we want things like `0 if True else 1.1` to be typed as `float`.
    However, because we process the input from left-to-right, the type varialbe in the
    polymorphic if-then-else operator will get assigned to `int` first.
    So we need to see if `α` has been assigned to a subtype of `t` and upgrade them.

    There might be a better way to do this.
    -/
    match t with
    | .prim _ (.numeric .float) => return Γ.upgradeToFloat α
    | _ => return Γ
  }
  return (cL ++ [ContextElem.existsSolved α t] ++ cR)

mutual

partial def instantiateL (Γ : Context) (span : Span) (α : Ident) (rhs : Typ) : ElabM Context := withSpan span do
  Γ.typewf (.evar span α)
  Γ.typewf rhs
  match ← Γ.solve α rhs with
  | some c => return c
  | none =>
    match rhs with
    | .evar _ β =>
      if Γ.ordered α β then
        let some Γ ← Γ.solve β (.evar span α) | throwType s!"cannot substitute {rhs}"
        return Γ
      else
        let some Γ ← Γ.solve α rhs | throwType s!"cannot substitute {rhs}"
        return Γ
    | .func _ params ret =>
      let params' ← params.mapM fun _ => freshName
      let ret' ← freshName
      let α' := Typ.func span (params'.map (.evar span)) (.evar span ret')
      let Θ : Context :=
        #[ContextElem.exists ret'] ++ (params'.reverse.map ContextElem.exists) ++ #[.existsSolved α α']
      let some Θ := Γ.insertAt (.exists α) Θ | throwType s!"failed to update context"
      let Θ ← (params.zip params').foldlM (fun Γ (p, p') => instantiateR Γ p.span (Γ.apply p) p') Θ
      instantiateL Θ ret.span ret' (Θ.apply ret)
    | .forall _ names body =>
      let namePairs ← names.mapM fun name => return (name, ← freshName)
      let Γ := Γ ++ namePairs.map fun (_, name) => ContextElem.forall name
      let Θ ← instantiateL Γ body.span α (body.applySubsts (namePairs.map fun (name, name') => (name, .var span name')))
      /- TODO: optimize this -/
      return namePairs.foldl (fun Θ (_, β') => Θ.dropMarker (.forall β')) Θ
    | _ => throwType s!"subtituting this polytype {rhs} not supported"

partial def instantiateR (Γ : Context) (span : Span) (lhs : Typ) (α : Ident) : ElabM Context := withSpan span do
  Γ.typewf lhs
  Γ.typewf (.evar span α)
  match ← Γ.solve α lhs with
  | some c => return c
  | none =>
    match lhs with
    | .evar _ β =>
      if Γ.ordered α β then
        let some Γ ← Γ.solve β (.evar span α) | throwType s!"cannot subtitute {lhs}"
        return Γ
      else
        let some Γ ← Γ.solve α lhs | throwType s!"cannot substitute {lhs}"
        return Γ
    | .func _ params ret =>
      let params' ← params.mapM fun _ => freshName
      let ret' ← freshName
      let α' := Typ.func span (params'.map (.evar span)) (.evar span ret')
      let Θ : Context :=
        #[ContextElem.exists ret'] ++ (params'.reverse.map ContextElem.exists) ++ #[.existsSolved α α']
      let some Θ := Γ.insertAt (.exists α) Θ | throwType s!"failed to update context"
      let Θ ← (params.zip params').foldlM (fun Γ (p, p') => instantiateL Γ p.span p' (Γ.apply p)) Θ
      instantiateR Θ ret.span (Θ.apply ret) ret'
    | .forall _ names body =>
      let namePairs ← names.mapM fun name => return (name, ← freshName)
      let Γ := namePairs.foldl (fun Γ (_, β') => Γ ++ #[.marker β', .exists β']) Γ
      let Θ ← instantiateR Γ body.span (body.applySubsts (namePairs.map fun (name, name') => (name, .evar span name'))) α
      /- TODO: optimize this -/
      return namePairs.foldl (fun Θ (_, β') => Θ.dropMarker (.marker β')) Θ
    | _ => throwType s!"substituting this polytype {lhs} is not supported"

end

/-- Check if `lhs` is a subtyp of `rhs`. -/
partial def subtype (Γ : Context) (lhs rhs : Typ) : ElabM Context := do
  Γ.typewf lhs
  Γ.typewf rhs
  match lhs, rhs with
  | .var _ x, .var span y =>
    if x == y then return Γ else
    withSpan span (throwType s!"{y} does not match {x}")
  | .evar span x, .evar _ y =>
    let occurs := Γ.existentials.contains x
    if x == y && occurs then return Γ else
    if occurs then
      instantiateL Γ span x rhs
    else
      withSpan span (throwType s!"{x} is not bound in the type context")
  | .evar span x, rhs =>
    if Γ.existentials.contains x && !rhs.ftv.contains x then
      instantiateL Γ span x rhs
    else
      withSpan span (throwType s!"substitution of {x} is invalid")
  | lhs, .evar span y =>
    if Γ.existentials.contains y && !lhs.ftv.contains y then
      instantiateR Γ span lhs y
    else
      withSpan span (throwType s!"substitution of {y} is invalid")
  | lhs, .forall span names body =>
    let namePairs ← names.mapM fun name => return (name, ← freshName)
    let substs : Substitutions := namePairs.map fun (name, name') => (name, .var span name')
    let body := body.applySubsts substs
    let fvars := namePairs.map fun (_, name) => ContextElem.forall name
    let c' ← subtype (Γ ++ fvars) lhs body
    /- TODO: optimize this -/
    return fvars.foldl (fun c fv => c.dropMarker fv) c'
  | .forall span names body, rhs =>
    let namePairs ← names.mapM fun name => return (name, ← freshName)
    let substs : Substitutions := namePairs.map fun (name, name') => (name, .evar span name')
    let body := body.applySubsts substs
    let c' := namePairs.foldl (fun c (_, name) => c ++ #[(.marker name), (.exists name)]) Γ
    let c' ← subtype c' body rhs
    /- TODO: optimize this -/
    return namePairs.foldl (fun c (_, ev) => c.dropMarker (.marker ev)) c'
  | .prim span p1, .prim _ p2 => do
    if (p1 == .numeric .int && p2 == .numeric .float) || p1 == p2 then
      return Γ
    else
      withSpan span (throwType s!"expected {p2}, got {p1}")
  | .func span paramsLhs retLhs, .func _ paramsRhs retRhs =>
    let lhsLen := paramsLhs.length
    let rhsLen := paramsRhs.length
    if lhsLen ≠ rhsLen then withSpan span (throwType s!"wrong number of arguments, got {lhsLen} but expected {rhsLen}") else
    let c ← (paramsLhs.zip paramsRhs).foldlM (fun c (lhs, rhs) => subtype c (c.apply rhs) (c.apply lhs)) Γ
    subtype c retLhs retRhs
  | .size span n, .size _ m => do
    if n != m then
      withSpan span (throwType s!"expected size to be {m}, got {n}")
    else
      return Γ
  | .shape span lhs, .shape _ rhs =>
    let lhsLen := lhs.length
    let rhsLen := rhs.length
    if lhsLen ≠ rhsLen then
      withSpan span (throwType s!"tensor rank mismatch, expected rank {rhsLen}, got rank {lhsLen}")
    else
      (lhs.zip rhs).foldlM (fun c (lhs, rhs) => subtype c (c.apply lhs) (c.apply rhs)) Γ
  | .tuple span lhs, .tuple _ rhs =>
    let lhsLen := lhs.length
    let rhsLen := rhs.length
    if lhsLen ≠ rhsLen then
      withSpan span (throwType s!"tuple length mismatch, expected length {rhsLen}, got length {lhsLen}")
    else
      (lhs.zip rhs).foldlM (fun c (lhs, rhs) => subtype c (c.apply lhs) (c.apply rhs)) Γ
  | .list _ lhs, .list _ rhs => subtype Γ lhs rhs
  | .tensor _ sh1 dt1, .tensor _ sh2 dt2 =>
    let c ← subtype Γ sh1 sh2
    subtype c dt1 dt2
  | .iter _ lhs, .iter _ rhs => subtype Γ lhs rhs
  | .sizeAdd span _ _, _
  | _, .sizeAdd span _ _ => withSpan span (throwUnsupported "adding sizes")
  | .shapeAppend span _ _, _
  | _, .shapeAppend span _ _ => withSpan span (throwUnsupported "appending shapes")
  | lhs, rhs => withSpan lhs.span (throwType s!"{lhs} is not a subtype of {rhs}")

/-! # -----------End: Type Checking Utilities -------------- -/



/-! # -----------Start: Elaborating Python to NKI -------------- -/

def value : Py.Value → ElabM Value
  | .none     => return .none
  | .bool   v => return .bool   v
  | .int    v => return .int    v
  | .float  v => return .float  v
  | .string v => return .string v
  | .ellipsis => throwType "ellipsis only allowed in tensor index"

def nonNumericBinOp : Py.BinOp → ElabM Builtin
  | .land       => return .land
  | .lor        => return .lor
  | .ne         => return .ne
  | .eq         => return .eq
  | .rshift     => return .rshift
  | .lshift     => return .lshift
  | .bitwiseAnd => return .bitwiseAnd
  | .bitwiseXor => return .bitwiseXor
  | .bitwiseOr  => return .bitwiseOr
  | .matmul     => return .matmul
  | _           => throwInternal "nonNumericBinOp should not be called on this operator"

def numericBinOp (n : Numeric) : Py.BinOp → ElabM Builtin
  | .floor => return .floor n
  | .pow   => return .pow n
  | .mod   => return .mod n
  | .div   => return .div n
  | .mul   => return .mul n
  | .sub   => return .sub n
  | .add   => return .add n
  | .ge    => return .ge n
  | .gt    => return .gt n
  | .le    => return .le n
  | .lt    => return .lt n
  | _      => throwInternal "numericBinOp should not be called on this operator"

partial def applyTypArgs (args : List Typ) : Typ → ElabM (List Typ × Typ)
  | .forall span αs body => do
    if args.length < αs.length then withSpan span (throwType "incorrect number of type arguments") else
    let polies := args.filter (not ∘ Typ.isMonotype)
    if let some poly := polies.head? then withSpan poly.span (throwType s!"cannot substitute a polymorphic type: {poly}") else
    let subs : Substitutions := (αs.zip args).reverse
    let body := body.applySubsts subs
    applyTypArgs (args.drop αs.length) body
  | .func span params ret =>
    if h : args.length > 0 then withSpan args[0].span (throwType s!"unexpected type argument {args[0]}") else
    return (params, ret)
  | t => withSpan t.span (throwType s!"got type {t}, expected function type")

partial def inferTypArgs (Γ : Context) (arrTyp : Typ) (numArgs : Nat) (typArgs : List Typ := []) : ElabM (List Typ × List Typ × Typ × Context) := do
  Γ.typewf arrTyp
  match arrTyp with
  | .forall span αs body =>
    let αs' ← αs.mapM fun _ => freshName
    let Θ := Γ ++ (αs'.map ContextElem.exists)
    let subs : Substitutions := (αs.zip (αs'.map (.evar span))).reverse
    let body := body.applySubsts subs
    inferTypArgs Θ body numArgs (typArgs ++ (αs'.map (.evar span)))
  | .evar span α =>
    let params ← (List.range numArgs).mapM fun _ => freshName
    let ret ← freshName
    let paramTyps := params.map (Typ.evar span)
    let retTyp := Typ.evar span ret
    let Θ : Context := #[.exists ret] ++ (params.reverse.toArray.map .exists) ++ #[.existsSolved α (.func span paramTyps retTyp)]
    let some Θ := Γ.insertAt (.exists α) Θ | throwType s!"failed to update context at {α}"
    return (typArgs, paramTyps, retTyp, Θ)
  | .func _ params ret =>
    return (typArgs, params, ret, Γ)
  | t => withSpan t.span (throwType s!"expected function type, got {t}")

mutual

partial def args (Γ : Context) : List Py.Arg → List Typ → ElabM (List Exp × List Typ × Context)
  | [], [] => return ([], [], Γ)
  | { keyword, val } :: aTl, tHd :: tTl => do
    if keyword.isSome then throwUnsupported "keyword arguments" else
    let (val, t, Γ) ← exp val Γ tHd
    let (aTl, tTl, Γ) ← args Γ aTl tTl
    return (val :: aTl, t :: tTl, Γ)
  | hd :: _, [] => withSpan hd.val.span (throwType "unexpected extra argument")
  | [], hd :: _ => throwType s!"missing argument of type {hd}"

partial def expList (es : List Py.Exp) (ts : List (Option Typ)) (Γ : Context) : ElabM (List Exp × List Typ × Context) := do
  match es, ts with
  | [], [] => return ([], [], Γ)
  | eHd :: eTl, tHd :: tTl =>
    let (eHd, tHd, Γ) ← exp eHd Γ tHd
    let (eTl, tTl, Γ) ← expList eTl tTl Γ
    return (eHd :: eTl, tHd :: tTl, Γ)
  | hd :: _, [] => withSpan hd.span (throwType s!"too many expressions")
  | [], _ :: _ => throwType s!"missing expressions"

/-- NOTE: We don't check for subsumption of the expected result type here, that's checked by `exp'` -/
partial def mkApp (f : Exp) (arrTyp : Typ) (typArgs : List Py.Exp) (as : List Py.Arg) (Γ : Context) : ElabM (Exp × Typ × Context) := do
  let typArgs ← typArgs.mapM typ
  let (typArgs, params, ret, Γ) ←
    if !typArgs.isEmpty then
      let (params, ret) ← applyTypArgs typArgs arrTyp
      pure (typArgs, params, ret, Γ)
    else
      inferTypArgs Γ arrTyp as.length
  let (as, _, Γ) ← args Γ as params
  let typArgs := Γ.apply <$> typArgs
  let ret := Γ.apply ret
  return (.call (← getSpan!) f typArgs as, ret, Γ)

partial def exp' (e : Py.Exp') (Γ : Context) (expected : Option Typ := none) : ElabM (Exp × Typ × Context) := do
  let span ← getSpan!
  let (e, typ, Γ) ←
    match e with
    | .var name =>
      -- TODO: lookup a list of builtin functions here
      let some found := Γ.findVarType name | throwType s!"variable not in scope"
      let e := .var span name
      pure (e, found, Γ)
    | .value v =>
      let v ← value v
      let e := Exp.value span v
      let checked := v.typ span
      pure (e, checked, Γ)
    | .unaryOp op x => do
      match op with
      | .pos =>
        let (x, xTyp, Γ) ← exp x Γ
        let Γ ← subtype Γ xTyp (floatTyp span)
        pure (x, Γ.apply xTyp, Γ)
      | .neg =>
        let (x, xTyp, Γ) ← exp x Γ
        let Γ ← subtype Γ xTyp (floatTyp span)
        let xTyp := Γ.apply xTyp
        let op ←
          match xTyp with
          | .prim _ (.numeric .int) => pure (Builtin.neg .int)
          | .prim _ (.numeric .float) => pure (Builtin.neg .float)
          | _ => throwType s!"type mismatch, got {xTyp}, expected int or float"
        pure (.call span (.builtin span op) [] [x], xTyp, Γ)
      | .bitwiseNot =>
        let (x, xTyp, Γ) ← exp x Γ (intTyp span)
        pure (.call span (.builtin span .bitwiseNot) [] [x], xTyp, Γ)
      | .lnot =>
        let (x, xTyp, Γ) ← exp x Γ (boolTyp span)
        pure (.call span (.builtin span .lnot) [] [x], xTyp, Γ)
    | .binOp op x y => do
      match op with
      -- -- logical
      | .land | .lor =>
        let (x, _, Γ) ← exp x Γ (boolTyp x.span)
        let (y, _, Γ) ← exp y Γ (boolTyp y.span)
        let op ← nonNumericBinOp op
        pure (.call span (.builtin span op) [] [x, y], boolTyp span, Γ)
      -- bitwise
      | .bitwiseOr | .bitwiseXor | .bitwiseAnd
      | .lshift | .rshift =>
        let (x, _, Γ) ← exp x Γ (intTyp x.span)
        let (y, _, Γ) ← exp y Γ (intTyp y.span)
        let op ← nonNumericBinOp op
        pure (.call span (.builtin span op) [] [x, y], intTyp span, Γ)
      -- comparison
      | .eq | .ne =>
        let op ← nonNumericBinOp op
        let arrTyp := op.typ span
        mkApp (.builtin span op) arrTyp [] [{val := x}, {val := y}] Γ
      -- arithmetic comparison
      | .lt | .le | .gt | .ge
      -- arithmetic
      | .add | .sub | .mul | .div
      | .mod | .pow | .floor =>
        let (x, xTyp, Γ) ← exp x Γ
        let (y, yTyp, Γ) ← exp y Γ
        let Γ ← subtype Γ xTyp (floatTyp span)
        let Γ ← subtype Γ (Γ.apply yTyp) (floatTyp span)
        let yTyp := Γ.apply yTyp
        let n : Numeric :=
          match xTyp, yTyp with
          | .prim _ (.numeric .float), _
          | _, .prim _ (.numeric .float) => .float
          | _, _ => .int
        let op ← numericBinOp n op
        pure (.call span (.builtin span op) [] [x, y], numericTyp span n, Γ)
      | .matmul => throwUnsupported "matmul"
    | .tuple es => do
      let expectedTyps : List (Option Typ) ←
        match expected with
        | none => pure (List.replicate es.length none)
        | some (.tuple span expected) =>
          if expected.length ≠ es.length then
            withSpan span (throwType s!"expected tuple with {expected.length} elements, got one with {es.length} elements")
          else
            pure (expected.map some)
        | some t => withSpan t.span (throwType s!"expected tuple, got {t}")
      let (es, ts, Γ) ← expList es expectedTyps Γ
      pure (.tuple span es, .tuple span ts, Γ)
    | .list es => do
      let expectedTyps : List (Option Typ) ←
        match expected with
        | none => pure (List.replicate es.length none)
        | some (.list _ t) => pure (List.replicate es.length (some t))
        | some t => withSpan t.span (throwType s!"expected list type, got {t}")
      let (es, ts, Γ) ← expList es expectedTyps Γ
      let α ← freshName
      let Γ := Γ.push (.exists α)
      let Γ ← ts.foldlM (fun Γ t => subtype Γ (.evar span α) (Γ.apply t)) Γ
      pure (.list span es, .list span (Γ.apply (.evar span α)), Γ)
    | .ifExp test body orelse => do
      let f : Exp := .builtin span .ite
      let arrTyp := Builtin.ite.typ span
      mkApp f arrTyp [] [{val := test}, {val := body}, {val := orelse}] Γ
    | .call f typArgs as => do
      let (f, arrTyp, Γ) ← exp f Γ
      mkApp f arrTyp typArgs as Γ
    | .access _ _ =>
      throwUnsupported "subscript expression"
    | .attr _ _ =>
      throwUnsupported "attribute access"
  match expected with
  | some expected =>
    let Γ ← subtype Γ typ expected
    return (e, Γ.apply typ, Γ)
  | none => return (e, typ, Γ)

partial def exp (e : Py.Exp) (Γ : Context) (expected : Option Typ := none) : ElabM (Exp × Typ × Context) :=
  match e with
  | { span, exp } => withSpan span do exp' exp Γ expected

end

/--
NOTE: no correctness check is done here
-/
partial def Typ.applyArr (arr : Typ) (typArgs : List Typ) (args : List Typ) : Option Typ :=
  match arr with
  | .forall _ names body =>
    if names.length > typArgs.length then none else
    let subs : Substitutions := (names.zip typArgs).reverse
    let body := body.applySubsts subs
    body.applyArr (typArgs.drop names.length) args
  | .func _ params ret =>
    if args.length > params.length then none else
    if args.length = params.length then ret else
    ret.applyArr [] (args.drop params.length)
  | _ => none

def Exp.typ (e : Exp) (Γ : Context) : ElabM Typ :=
  match e with
  | .var _ id => do
    let some t := Γ.findVarType id | throwType s!"variable {id} cannot be found in the context"
    return t
  | .value span val => return val.typ span
  | .builtin span val => return val.typ span
  | .tuple span es => (.tuple span ·) <$> (es.mapM (Exp.typ · Γ))
  | .list span es => do
    let es ← es.mapM (Exp.typ · Γ)
    (Typ.list span ·) <$> es.head?
  | .call _ f typArgs args => do
    let arrT ← f.typ Γ
    let argsT ← args.mapM (Exp.typ · Γ)
    arrT.applyArr typArgs argsT

/--
`desired` is the type the user wants, used to "admit" a definition using `pass`
-/
def Stmt.typ (s : Stmt) (Γ : Context) (desired : Typ) : ElabM Typ :=
  match s with
  | .seq _ _ s2 => s2.typ Γ desired
  | .exp span _ => return noneTyp span
  | .ret _ e => e.typ Γ
  | .letBind _ name typ _ body =>
    /-
    NOTE: we have to re-introduce the variable in the context because it is
    dropped after the let-assignment statement has been elaborated.
    -/
    body.typ (Γ ++ #[.var name typ]) desired
  | .assign span _ _ => return noneTyp span
  | .assert span _ => return noneTyp span
  | .funcDef _ _ t _ => return t
  | .ifStm _ _ thn els =>
    match els with
    | some els => do
      let t1 ← thn.typ Γ desired
      let t2 ← els.typ Γ desired
      return t1.min t2
    | none => thn.typ Γ desired
  | .forLoop span _ _ _ => return noneTyp span
  | .whileLoop span _ _ => return noneTyp span
  | .pass _ => return desired
  | .breakLoop span => return noneTyp span
  | .continueLoop span => return noneTyp span

def Stmt.append (s1 : Stmt) : Option Stmt → Stmt
  | some s2 => .seq ⟨s1.span.pos, s2.span.stopPos⟩ s1 s2
  | none    => s1

mutual

def stmts? : Option (List Py.Stmt) → Context → ElabM (Option Stmt × Context)
  | some s, Γ => do
    let (some s, Γ) ← stmts s Γ | throwEmptyStmts
    return (some s, Γ)
  | none, Γ => return (none, Γ)
termination_by s => sizeOf s

def elseIfs (elifs : List (Py.Exp × List Py.Stmt)) (els : Option (List Py.Stmt)) (Γ : Context) : ElabM (Option Stmt × Context) := do
  match elifs with
  | [] => stmts? els Γ
  | (cond, thn) :: tl =>
    let span ← getSpan!
    let (cond, _, Γ) ← exp cond Γ (boolTyp span)
    let (some thn, Γ) ← stmts thn Γ | throwEmptyStmts
    let (els, Γ) ← elseIfs tl els Γ
    return (some (.ifStm span cond thn els), Γ)
termination_by sizeOf elifs + sizeOf els

def funcDef (func : Py.FuncDef) (Γ : Context) : ElabM (Stmt × Context) := do
  match func with
  | { name, typParams, params, returns, body, decorators } =>
    if !decorators.isEmpty then throwUnsupported "decorators" else
    let span ← getSpan!

    /- Compute the context extension needed -/
    let Θ : Context := typParams.toArray.map .forall
    let (paramTyps, Θ) ← params.foldlM (fun (pts, Θ) { typ := t, name, dflt } => do
      if Option.isSome dflt then throwUnsupported "default argument" else
      match t with
      | some t =>
        let t ← typ t
        return (pts.push t, Θ.push (.var name t))
      | none =>
        let α ← freshName
        let t := .evar span α
        return (pts.push t, Θ ++ #[.exists α, .var name t])
    ) (#[], Θ)

    let (retTyp, Θ) ←
      match returns with
      | some returns => pure (← typ returns, Θ)
      | none =>
        let α ← freshName
        pure (.evar span α, Θ.push (.exists α))

    let markerName ← freshName
    let Γ : Context := Γ ++ #[.marker markerName] ++ Θ

    let (some body, Γ) ← withRetTyp retTyp (stmts body Γ) | throwEmptyStmts

    let retTyp := Γ.apply retTyp
    /-
    Need to double check here to make sure if-statements are typed properly
    -/
    let Γ ← subtype Γ (← body.typ Γ retTyp) retTyp
    let retTyp := Γ.apply retTyp
    let funTyp := Γ.apply (Typ.func span paramTyps.toList retTyp)

    let some (Γ, Γ') := Γ.breakMarker (.marker markerName) | throwInternal "marker not found in context"
    let genArgs := (Γ'.unsolved).toList
    let finalTyp :=
      if genArgs.isEmpty then
        if typParams.isEmpty then funTyp else .forall span typParams funTyp
      else
        /-
        TODO: rename the inferred type parameters to be more user friendly.
        Need to be careful about capture avoidance while doing so.
        -/
        let subs : Substitutions := genArgs.map fun α => (α, .var span α)
        let body := funTyp.applySubsts subs
        .forall span (genArgs ++ typParams) body

    return (.funcDef span name finalTyp body, Γ ++ #[.var name finalTyp])
termination_by sizeOf func

/--
NOTE: Do not lift the call to `stmts k` up to the top of the function!
This is becase some statements needs to modify the typing context before
evaluating the continutation.
-/
def stmt' (s : Py.Stmt') (k : List Py.Stmt) (Γ : Context) : ElabM (Stmt × Context) := do
  let span ← getSpan!
  match s with
  | .exp e =>
    let (e, _, Γ) ← exp e Γ
    let (k, Γ) ← stmts k Γ
    return ((Stmt.exp span e).append k,  Γ)
  | .imprt _ _ | .imprtFrom _ _ _ =>
    throwUnsupported "import statements"
  | .ret e =>
    let (e, t, Γ) ← exp e Γ
    let some retTyp ← getRetTyp | throwType "\'return\' not allowed outside function contexts"
    /-
    TODO: The way we check and update the return type here makes this valid program a type error:
    ```
    def ite():
      if True:
        return 0
      else:
        return 0.
    ```
    This function should have type `func[float]`, but we get a type error in the else branch
    because the return type has already be set to `int`. We need to somehow carefully generalize
    the return type here.
    -/
    let Γ ← subtype Γ t retTyp
    applyCtxToRet Γ
    let (k, Γ) ← stmts k Γ
    return ((Stmt.ret span e).append k, Γ)
  | .assign lhs anno rhs =>
    let anno ← anno.mapM typ
    let (rhs, t, Γ) ← exp rhs Γ anno
    match lhs with
    | ⟨span, .var name⟩ =>
      /- If name collisions were an issue, we would subtitute `name` in `rhs`
         with a fresh variable. But our generated name never clashes with
         user defined identifiers. So we simply make a marker here to know
         which part of the output context to drop. -/
      let α ← freshName
      let Γ := Γ ++ #[.marker α, .var name t]
      let (k, Γ) ← stmts k Γ
      let k := k.getD (.exp span (.value span .none))
      let some (Γ, _) := Γ.breakMarker (.marker α) | throwInternal "failed to find marker defined before"
      /- Note that we do not generalize let-bindings as in other let-polymorphic type systems.
         This decision can be revisited later. -/
      return (Stmt.letBind span name t rhs k, Γ)
    | _ => throwUnsupported "complex assignments"
  | .assert e =>
    let (e, t, Γ) ← exp e Γ
    let Γ ← subtype Γ t (boolTyp span)
    let (k, Γ) ← stmts k Γ
    return ((Stmt.assert span e).append k, Γ)
  | .funcDef dfn =>
    let (dfn, Γ) ← funcDef dfn Γ
    let (k, Γ) ← stmts k Γ
    return (dfn.append k, Γ)
  | .ifStm cond thn elifs els =>
    let (cond, _, Γ) ← exp cond Γ (boolTyp span)
    let (some thn, Γ) ← stmts thn Γ | throwEmptyStmts
    let (els, Γ) ← elseIfs elifs els Γ
    let (k, Γ) ← stmts k Γ
    return ((Stmt.ifStm span cond thn els).append k, Γ)
  | .forLoop pat iter body =>
    match pat with
    | .var name =>
      let α ← freshName
      let Γ := Γ ++ #[.marker α, .exists α]
      let (iter, _, Γ) ← exp iter Γ (Typ.iter span (.evar span α))
      let (some body, Γ) ← withLoop (stmts body Γ) | throwEmptyStmts
      let (k, Γ) ← stmts k Γ
      let some (Γ, _) := Γ.breakMarker (.marker α) | throwInternal "cannot find marker in context"
      return ((Stmt.forLoop span (.var name) iter body).append k, Γ)
    | .tuple _ =>
      throwUnsupported "tuple patterns"
  | .whileLoop cond body =>
    let (cond, _, Γ) ← exp cond Γ (boolTyp span)
    let (some body, Γ) ← withLoop (stmts body Γ) | throwEmptyStmts
    let (k, Γ) ← stmts k Γ
    return ((Stmt.whileLoop span cond body).append k, Γ)
  | .pass =>
    let (k, Γ) ← stmts k Γ
    return ((Stmt.pass span).append k, Γ)
  | .breakLoop =>
    if !(← inLoop) then throwType "\'break\' only allowed in loops" else
    let (k, Γ) ← stmts k Γ
    return ((Stmt.breakLoop span).append k, Γ)
  | .continueLoop =>
    if !(← inLoop) then throwType "\'continue\' only allowed in loops" else
    let (k, Γ) ← stmts k Γ
    return ((Stmt.continueLoop span).append k, Γ)
termination_by sizeOf s + sizeOf k

def stmt (s : Py.Stmt) (k : List Py.Stmt) (Γ : Context) : ElabM (Stmt × Context) := do
  match s with
  | { stmt, span } => withSpan span do stmt' stmt k Γ
termination_by sizeOf s + sizeOf k

def stmts (k : List Py.Stmt) (Γ : Context) : ElabM (Option Stmt × Context) := do
  match k with
  | [] => return (none, Γ)
  | hd :: tl =>
    let (s, Γ) ← stmt hd tl Γ
    return (some s, Γ)
termination_by sizeOf k

end

/-! # -----------End: Elaborating Python to NKI -------------- -/

def infer (info : FileInfo) (p : Py.Prog) : Except String Context :=
  match (stmts p.stmts #[]).run info {} with
  | .ok (_, c) _ => .ok c
  | .error msg _ => .error msg

def run (input : String) (fileName : String) (fileMap : Lean.FileMap := input.toFileMap) : Except String String := do
  let prog ← Py.Parser.run input fileName fileMap
  let c ← infer { content := input, fileName, fileMap } prog
  return "\n".intercalate (c.toList.map ContextElem.toString)
