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
- Kind validation.
  We currently run kind checking after inferring the type of a function def.
  However, we pass it a empty kind context when doing so, this fails when
  a nested `def` refers to a type variable bound earlier.
  We should also think about whether `dtype` should be a separate kind.
- Better handling of when to apply the context to substitute types.
- Unification: This implementation does not perform unification to handle
  more complex constraints over longer code spans. This might also fixes
  the issue above of better handling of when to actually apply subsitutions
  obtained from the context.
- Unimplemented language features, grep for calls of `throwUnsupported`
- Semantic subtyping.
  For example, if a function expects: `∀ DT M N, tensor[DT, (M, N, M + N)]`,
  passing it `tensor[int, (10, 20, 30)]` should be allowed.
- Better handling of subtyping coercions.
  See comments in `Context.solve` and `stmt'` in the `ret` case.
- Better error reporting in general.
- More nuanced reporting of subtyping. For example, if either a float
  or an int can be used, we default to a float.
- Other todos marked by `TODO` comments.
-/

/-! # -----------Start: Parsing Type Annotations-------------- -/

def prim : Py.Prim → Prim
  | .none => .none
  | .bool => .bool
  | .numeric .int => .numeric .int
  | .numeric .float => .numeric .float
  | .string => .string
  | .dtype dt => .dtype dt

mutual

def typ' (span : Span) (t : Py.Typ') : Typ :=
  match t with
  | .var id => .var span id
  | .forall names body => .forall span (names.map (⟨·, []⟩)) (typ body)
  | .prim p => .prim span (prim p)
  | .func params ret => .func span (params.map typ) (typ ret)
  | .size n => .size span n
  | .shape dims => .shape span (dims.map typ)
  | .tuple typs => .tuple span (typs.map typ)
  | .list t => .list span (typ t)
  | .tensor sh dt => .tensor span (typ sh) (typ dt)
  | .iter t => .iter span (typ t )
  | .sizeAdd x y => .sizeAdd span (typ x) (typ y)
  | .shapeAppend s1 s2 => .shapeAppend span (typ s1) (typ s2)

def typ : Py.Typ → Typ
  | { span, typ := t } => typ' span t

end

/-! # -----------End: Parsing Type Annotations-------------- -/


/-! # -----------Start: Type Checking Utilities -------------- -/

abbrev KindCtx := Array (Array (Ident × Kind))

def KindCtx.pop (Φ : KindCtx) : KindCtx := Array.pop Φ

def KindCtx.push (Φ : KindCtx) (names : List Ident) : KindCtx :=
  Array.push Φ (names.toArray.map fun name => (name, .unknown))

def KindCtx.get? (Φ : KindCtx) (name : Ident) : Option Kind := do
  for i in (List.finRange Φ.size).reverse do
    let Γ := Φ[i]
    for j in (List.finRange Γ.size).reverse do
      let (name', kind) := Γ[j]
      if name' == name then
        return kind
  none

def KindCtx.update (Φ : KindCtx) (name : Ident) (kind : Kind) : KindCtx := Id.run do
  let mut Φ := Φ
  for i in (List.finRange Φ.size).reverse do
    let Γ := Φ[i]
    for j in (List.finRange Γ.size).reverse do
      let (name', _) := Γ[j]
      if name' == name then
        let Γ := Γ.set j (name, kind)
        return Φ.set i Γ
  return Φ

/--
Check if a type is kind correct.
NOTE: where bounds are ignored
-/
def Typ.checkKind (expected : Kind) (Φ : KindCtx) : Typ → ElabM KindCtx
  | .var span id | .evar span id => withSpan span do
    match Φ.get? id with
    | some k =>
      if k == .unknown then
        return Φ.update id expected
      else
        if k == expected then
          return Φ
        else
          throwType s!"kind mismatch, expected {expected}, got {k}"
    | none => return Φ--throwType s!"unbound type variable {id}"
  | .forall span vars body => do
    if expected != .typ then withSpan span (throwType s!"kind mismatch, expected {expected}, got type") else
    let Ψ ← body.checkKind .typ (Φ.push (vars.map TypVar.name))
    return Ψ.pop
  | .prim span _ =>
    if expected == .typ then
      return Φ
    else
      withSpan span (throwType s!"kind mismatch, expected {expected}, got type")
  | .func span params ret => do
    if expected != .typ then withSpan span (throwType s!"kind mismatch, expected {expected}, got type") else
    let Φ ← params.foldlM (Typ.checkKind .typ) Φ
    ret.checkKind .typ Φ
  | .size span _ =>
    if expected == .size then
      return Φ
    else
      withSpan span (throwType s!"kind mismatch, expected {expected}, got size")
  | .shape span dims =>
    if expected != .shape then withSpan span (throwType s!"kind mismatch, expected {expected}, got shape. Did you mixed up the order of tensor shape and dtype?") else
    dims.foldlM (Typ.checkKind .size) Φ
  | .tuple span typs =>
    if expected != .typ then withSpan span (throwType s!"kind mismatch, expected {expected}, got type") else
    typs.foldlM (Typ.checkKind .typ) Φ
  | .list span t =>
    if expected != .typ then withSpan span (throwType s!"kind mismatch, expected {expected}, got type") else
    t.checkKind .typ Φ
  | .tensor span sh dt => do
    if expected != .typ then withSpan span (throwType s!"kind mismatch, expected {expected}, got type") else
    let Φ ← sh.checkKind .shape Φ
    /- TODO: do we want to enforce a special kind for dtypes? -/
    dt.checkKind .typ Φ
  | .iter span t => do
    if expected != .typ then withSpan span (throwType s!"kind mismatch, expected {expected}, got type") else
    t.checkKind .typ Φ
  | .sizeAdd span x y => do
    if expected != .size then withSpan span (throwType s!"kind mismatch, expected {expected}, got size") else
    let Φ ← x.checkKind .size Φ
    y.checkKind .size Φ
  | .shapeAppend span s1 s2 => do
    if expected != .shape then withSpan span (throwType s!"kind mismatch, expected {expected}, got shape") else
    let Φ ← s1.checkKind .shape Φ
    s2.checkKind .shape Φ

partial def Context.typewf (Γ : Context) (typ : Typ) : ElabM Unit := do
  match typ with
  | .var _ name =>
    if !Γ.foralls.contains name then
      throwType s!"type variable {name} not found in context"
  | .evar _ name =>
    if !Γ.existentials.contains name then
      throwType s!"meta variable {name} not found in context"
  | .forall _ vars body =>
    let c' := Γ ++ (vars.map fun ⟨x, _⟩ => .forall x).toArray
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
    | .forall _ vars body =>
      let namePairs ← vars.mapM fun {name, ..} => return (name, ← freshName)
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
    | .forall _ vars body =>
      let namePairs ← vars.mapM fun {name, ..} => return (name, ← freshName)
      let Γ := namePairs.foldl (fun Γ (_, β') => Γ ++ #[.marker β', .exists β']) Γ
      let Θ ← instantiateR Γ body.span (body.applySubsts (namePairs.map fun (name, name') => (name, .evar span name'))) α
      /- TODO: optimize this -/
      return namePairs.foldl (fun Θ (_, β') => Θ.dropMarker (.marker β')) Θ
    | _ => throwType s!"substituting this polytype {lhs} is not supported"

end

/-- Check if `lhs` is a subtype of `rhs`. -/
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
  | lhs, .forall span vars body =>
    let namePairs ← vars.mapM fun {name, ..} => return (name, ← freshName)
    let substs : Substitutions := namePairs.map fun (name, name') => (name, .var span name')
    let body := body.applySubsts substs
    let fvars := namePairs.map fun (_, name) => ContextElem.forall name
    let c' ← subtype (Γ ++ fvars) lhs body
    /- TODO: optimize this -/
    return fvars.foldl (fun c fv => c.dropMarker fv) c'
  | .forall span vars body, rhs =>
    let namePairs ← vars.mapM fun {name, ..} => return (name, ← freshName)
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
  | .forall span vars body => do
    let αs := vars.map TypVar.name
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
  | .forall span vars body =>
    let αs := vars.map TypVar.name
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
partial def mkApp (f : Exp) (arrTyp : Typ) (typArgs : List Py.Typ) (as : List Py.Arg) (Γ : Context) : ElabM (Exp × Typ × Context) := do
  let typArgs := typArgs.map typ
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
      | .lt | .le | .gt | .ge =>
        let (x, xTyp, Γ) ← exp x Γ
        let (y, yTyp, Γ) ← exp y Γ
        let Γ ← subtype Γ xTyp yTyp
        let xTyp := Γ.apply xTyp
        let Γ ← subtype Γ xTyp (floatTyp span)
        let Γ ← subtype Γ (Γ.apply yTyp) (floatTyp span)
        let yTyp := Γ.apply yTyp
        let n : Numeric :=
          match xTyp, yTyp with
          | .prim _ (.numeric .float), _
          | _, .prim _ (.numeric .float) => .float
          | _, _ => .int
        let op ← numericBinOp n op
        pure (.call span (.builtin span op) [] [x, y], boolTyp span, Γ)
      -- arithmetic
      | .add | .sub | .mul | .div
      | .mod | .pow | .floor =>
        let (x, xTyp, Γ) ← exp x Γ
        let (y, yTyp, Γ) ← exp y Γ
        let Γ ← subtype Γ xTyp yTyp
        let xTyp := Γ.apply xTyp
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
NOTE: No correctness check is done
-/
partial def Typ.applyArr (arr : Typ) (typArgs : List Typ) (args : List Typ) : Option Typ :=
  match arr with
  | .forall _ vars body =>
    if vars.length > typArgs.length then none else
    let names := vars.map TypVar.name
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
    return Γ.apply t
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
      return (Γ.apply t1).min (Γ.apply t2)
    | none => thn.typ Γ desired
  | .forLoop span _ _ _ => return noneTyp span
  | .whileLoop span _ _ => return noneTyp span
  | .pass _ => return desired
  | .breakLoop span => return noneTyp span
  | .continueLoop span => return noneTyp span

def Stmt.append (s1 : Stmt) : Option Stmt → Stmt
  | some s2 => .seq ⟨s1.span.pos, s2.span.stopPos⟩ s1 s2
  | none    => s1

abbrev BoundsCtx := Array (Ident × (Kind × List TypBound))

def BoundsCtx.get? (c : BoundsCtx) (name : Ident) : Option (Kind × List TypBound) := do
  for i in (List.finRange c.size).reverse do
    let (name', kbs) := c[i]
    if name' == name then return kbs
  none

def BoundsCtx.set (c : BoundsCtx) (name : Ident) (kind : Kind) (bounds : List TypBound) : BoundsCtx := Id.run do
  let mut c := c
  for i in (List.finRange c.size).reverse do
    let (name', _) := c[i]
    if name' == name then return Array.set c i (name, (kind, bounds))
  return c

def whereBound (c : BoundsCtx) (e : Py.Exp) : ElabM BoundsCtx := do
  match e with
  | ⟨_, .binOp .bitwiseOr ⟨factorSpan, .value (.int factor)⟩ ⟨varSpan, .var t⟩⟩ =>
    -- divisibility
    -- `n | t` where `n` is a nat and `t` is a type var
    if factor ≤ 0 then withSpan factorSpan (throwType "factor must be greater than 0") else
    let some (kind, bounds) := c.get? t | withSpan varSpan (throwType "unbound type variable")
    if kind != .size && kind != .unknown then withSpan varSpan (throwType s!"kind mismatch, expected size, got {kind}")
    return c.set t .size (.divisibleBy factor.toNat :: bounds)
  | ⟨_, .binOp .le ⟨varSpan, .var t⟩ ⟨upperSpan, .value (.int upper)⟩⟩ =>
    -- less-than-equal-to
    -- `t <= n` where `n` is a nat and `t` is a type var
    if upper ≤ 0 then withSpan upperSpan (throwType "upper bound must be greater than 0") else
    let some (kind, bounds) := c.get? t | withSpan varSpan (throwType "unbound type variable")
    if kind != .size && kind != .unknown then withSpan varSpan (throwType s!"kind mismatch, expected size, got {kind}")
    return c.set t .size (.le upper.toNat :: bounds)
  | e => withSpan e.span (throwType "unsupported where bound")

def Exp.checkWhereBounds (Γ : Context) (e : Exp) : ElabM Unit :=
  visit e
where
  visitList
  | [] => return
  | hd :: tl => do visit hd; visitList tl

  visit
  | .var _ _ => return
  | .value _ _ => return
  | .builtin _ _ => return
  | .tuple _ es => visitList es
  | .list _ es => visitList es
  | .call _ f typArgs args => do
    match ← f.typ Γ with
    | .forall span vars _ =>
      if vars.length ≠ typArgs.length then withSpan span (throwType "number of generic parameters does not match") else
      (vars.zip typArgs).forM fun (⟨_, bounds⟩, t) =>
        match t with
        | .size span n =>
          bounds.forM fun bound => do
            match bound with
            | .le m =>
              if n > m then
                withSpan span (throwType s!"size here must be less-than-equal-to {m}")
            | .divisibleBy m =>
              if n % m ≠ 0 then
                withSpan span (throwType s!"size here must be divisible by {m}")
        | .var _ _ => /- our analysis is conservative -/ return
        | t => do
          if !bounds.isEmpty then
            withSpan t.span (throwType "expected size here")
      visitList args
    | _ => return

/--
Check if where bounds are satisfied in type applications
-/
def Stmt.checkWhereBounds (Γ : Context) (s : Stmt) : ElabM Unit :=
  visit s
where
  visit
  | .seq _ s1 s2 => do visit s1; visit s2
  | .exp _ e => e.checkWhereBounds Γ
  | .ret _ e => e.checkWhereBounds Γ
  | .letBind _ _ _ rhs body => do rhs.checkWhereBounds Γ; visit body
  | .assign _ lhs rhs => do lhs.checkWhereBounds Γ; rhs.checkWhereBounds Γ
  | .assert _ e => do e.checkWhereBounds Γ
  | .funcDef _ _ _ body => do visit body
  | .ifStm _ cond thn els => do
    cond.checkWhereBounds Γ
    visit thn
    match els with
    | some els => visit els
    | none => return
  | .forLoop _ _ it body => do it.checkWhereBounds Γ; visit body
  | .whileLoop _ cond body => do cond.checkWhereBounds Γ; visit body
  | .pass _ => return
  | .breakLoop _ => return
  | .continueLoop _ => return

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
    let thnTyp ← thn.typ Γ (noneTyp span)
    let elsTyp := (← els.mapM (·.typ Γ (noneTyp span))).getD (noneTyp span)
    let Γ ←
      match thnTyp, elsTyp with
      | .prim _ .none, _
      | _, .prim _ .none => pure Γ
      | _, _ => subtype Γ thnTyp elsTyp
    return (some (.ifStm span cond thn els), Γ)
termination_by sizeOf elifs + sizeOf els

def funcDef (func : Py.FuncDef) (Γ : Context) : ElabM (Stmt × Context) := do
  match func with
  | { name, typParams, params, returns, body, decorators, whereBounds } =>
    if !decorators.isEmpty then throwUnsupported "decorators" else
    let span ← getSpan!

    /- Compute the context extension needed -/
    let Θ : Context := typParams.toArray.map .forall
    let (paramTyps, Θ) ← params.foldlM (fun (pts, Θ) { typ := t, name, dflt } => do
      if Option.isSome dflt then throwUnsupported "default argument" else
      match t with
      | some t =>
        let t := typ t
        return (pts.push t, Θ.push (.var name t))
      | none =>
        let α ← freshName
        let t := .evar span α
        return (pts.push t, Θ ++ #[.exists α, .var name t])
    ) (#[], Θ)

    let (retTyp, Θ) ←
      match returns with
      | some returns => pure (typ returns, Θ)
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

    /-
    Must do this after all type inference is complete

    TODO: find a better place to call this function.
    Currently, we are not checking top-level code outside function definitions.
    We are also not checking for default parameters because we need the context
    to include all the parameters declared for the function.
    -/
    _ ← body.checkWhereBounds Γ

    let some (Γ, Γ') := Γ.breakMarker (.marker markerName) | throwInternal "marker not found in context"
    let genArgs := (Γ'.unsolved)
    let (typParams, typBody) :=
      if genArgs.isEmpty then
        if typParams.isEmpty then (#[], funTyp) else (typParams.toArray, funTyp)
      else
        /-
        TODO: rename the inferred type parameters to be more user friendly.
        Need to be careful about capture avoidance while doing so.
        -/
        let subs : Substitutions := genArgs.toList.map fun α => (α, .var span α)
        let body := funTyp.applySubsts subs
        ((genArgs ++ typParams.toArray), body)

    /-
    TODO:
    First, we need to properly keep track of the kind of each type variable currently in bound.
    Here, we always pass an empty context which is fine until we need to check the type of a nested
    function definition.

    Second, we need the kind of each top-level type variable for the whereBounds, this is a bit of a hack to get it.
    -/
    let kindCtx ← typBody.checkKind .typ (KindCtx.push #[] typParams.toList)
    if h : kindCtx.size ≠ 1 then throwInternal "kind check returned the wrong number of scopes" else
    let kindCtx := kindCtx[0]

    let boundsCtx : BoundsCtx := kindCtx.map fun (name, kind) => (name, (kind, []))
    let boundsCtx ← whereBounds.foldlM (fun c e => whereBound c e) boundsCtx

    let typVars : List TypVar := boundsCtx.toList.map fun (id, (_, bounds)) => ⟨id, bounds⟩
    let finalTyp :=
      if typVars.isEmpty then typBody else .forall span typVars typBody

    let fd := .funcDef span name finalTyp body
    return (fd, Γ ++ #[.var name finalTyp])
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
    let anno := anno.map typ
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
    let thnTyp ← thn.typ Γ (noneTyp span)
    let elsTyp := (← els.mapM (·.typ Γ (noneTyp span))).getD (noneTyp span)
    let Γ ←
      match thnTyp, elsTyp with
      | .prim _ .none, _
      | _, .prim _ .none => pure Γ
      | _, _ => subtype Γ thnTyp elsTyp
    let (k, Γ) ← stmts k Γ
    return ((Stmt.ifStm span cond thn els).append k, Γ)
  | .forLoop pat iter body =>
    match pat with
    | .var name =>
      let α ← freshName
      let Γ := Γ ++ #[.marker α, .exists α, .var name (.evar span α)]
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

def typecheck (info : FileInfo) (p : Py.Prog) : Except String Context :=
  match (stmts p.stmts #[]).run info {} with
  | .ok (_, c) _ => .ok c
  | .error msg _ => .error msg

def runTypechecker (input : String) (fileName : String) (fileMap : Lean.FileMap := input.toFileMap) : Except String String := do
  let prog ← Py.Parser.run input fileName fileMap
  let c ← typecheck { content := input, fileName, fileMap } prog
  return "\n".intercalate (c.toList.map ContextElem.toString)
