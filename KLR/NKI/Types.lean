/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure
-/
import Aesop
import KLR.Core.Operators

/-!
# A type system for NKI

The polymorphic type system for NKI consisting of two sorts: `SNat` and `STyp`.

`SNat` represents the natural numbers used to denote tensor shapes.
`STyp` is the universe of types that includes tensors parametrized by `SNat`s.

All type parameters are universally quantified and must be given up front.
We then use De Bruijn indices in the form of `Fin` type to index type parameter binders.
To make things easier, we count indicies from the beginning:
`∀ a b, tuple[a, b]` ≡ `(STyp.tuple [SNat.param 0, SNat.param 1] : STyp 0 2)`
-/

theorem List.findIdx?_lt_of_eq_some {l : List α} : l.findIdx? p = some x → x < l.length := by
  intro h
  rw [List.findIdx?_eq_guard_findIdx_lt] at h
  aesop

namespace KLR.NKI

/--
A type universe for denoting tensor shapes.

`nnat` is the total number of universal quantifiers in scope.
-/
inductive SNat (nnat : Nat)
  | param (idx : Fin nnat)
  | const (n : Nat)

/--
The universe of types.

`nnat` is the total number of universal quantifiers in scope for `SNat`s.

`ntyp` is the total number of universal quantifiers in scope for `STyp`s.
-/
inductive STyp (nnat ntyp : Nat)
  | param (idx : Fin ntyp)
  | none
  | bool
  | int
  | float
  | string
  | tuple (typs : List (STyp nnat ntyp))
  -- This is needed for indexing into a tensor.
  -- But currently impossible to construct directly in the AST.
  | dtype (typ : Core.Dtype)
  | tensor (shape : List (SNat nnat)) (dtype : Core.Dtype)
  | func (dom ran : STyp nnat ntyp)

def String.joinSep (sep : String) (l : List String) : String :=
  match l with
  | [] => ""
  | [s] => s
  | hd :: tl => s!"{hd}{sep}{String.joinSep sep tl}"

def SNat.toString : SNat nnat → String
  | param idx => s!"s_{idx}"
  | const n => s!"{n}"

def STyp.toStringAux : STyp nnat ntyp → String
  | .param idx => s!"t_{idx}"
  | .none => "none"
  | .bool => "bool"
  | .int => "int"
  | .float => "float"
  | .string => "string"
  | .tuple typs =>
    let typs := String.joinSep ", " (typs.map STyp.toStringAux)
    s!"tuple[{typs}]"
  | .dtype typ => typ.toString
  | .tensor shapes typ =>
    let shapes := String.joinSep ", " (shapes.map SNat.toString)
    s!"tensor[{typ}, ({shapes})]"
  | .func dom ran => s!"{dom.toStringAux} → {ran.toStringAux}"

def STyp.toString (t : STyp nnat ntyp) : String :=
  let natParams := String.joinSep " " <| (List.range nnat).map (λ n => s!"s_{n}")
  let typParams := String.joinSep " " <| (List.range ntyp).map (λ t => s!"t_{t}")
  let header := s!"\{{natParams}} <{typParams}>"
  let body := t.toStringAux
  s!"{header} {body}"

instance : Repr (STyp nnat ntyp) where
  reprPrec t _ := t.toString

namespace Nominal
  /-!
  # An alternative types definition using nominal variable binding

  This requires a separate well-formedness proof to show that varaible references are valid.
  -/

  inductive Srt
    | snat
    | styp

  structure TypParam where
    name : String
    sort : Srt

  inductive SNat
    | param (name : String)
    | const (n : Nat)

  inductive STyp
    | param (name : String)
    | none
    | bool
    | int
    | float
    | string
    | tuple (typs : List STyp)
    | dtype (dtype : Core.Dtype)
    | tensor (shape : List SNat) (dtype : Core.Dtype)
    | func (dom ran : STyp)

  inductive Typ'
    | snat (sn : SNat)
    | styp (st : STyp)

  structure Typ where
    params : List TypParam
    typ : Typ'

  inductive SNat.WellFormed : List TypParam → SNat → Prop
    | param {ps : List TypParam} {name : String}
        : ⟨name, .snat⟩ ∈ ps → SNat.WellFormed ps (.param name)
    | const {ps : List TypParam} {n : Nat}
        : SNat.WellFormed ps (.const n)

  inductive STyp.WellFormed (ps : List TypParam) : STyp → Prop
    | param : ⟨name, .styp⟩ ∈ ps → STyp.WellFormed ps (.param name)
    | none : STyp.WellFormed ps .none
    | bool : STyp.WellFormed ps .bool
    | int : STyp.WellFormed ps .int
    | float : STyp.WellFormed ps .float
    | string : STyp.WellFormed ps .string
    | tuple : (∀ ty ∈ typs, STyp.WellFormed ps ty) → STyp.WellFormed ps (.tuple typs)
    | tensor : (∀ s ∈ shape, s.WellFormed ps) → STyp.WellFormed ps (.tensor shape typ)
    | func : STyp.WellFormed ps dom → STyp.WellFormed ps ran → STyp.WellFormed ps (.func dom ran)

  inductive Typ'.WellFormed : List TypParam → Typ' → Prop
    | snat : sn.WellFormed ps → Typ'.WellFormed ps (.snat sn)
    | styp : st.WellFormed ps → Typ'.WellFormed ps (.styp st)

  def Typ.WellFormed (t : Typ) : Prop :=
    t.typ.WellFormed t.params

  def Srt.isNat : Srt → Bool
    | .snat => true
    | .styp => false

  def Srt.isTyp : Srt → Bool
    | .snat => false
    | .styp => true

  def SNat.toDeBruijn (natParams : List String) : SNat → Option (NKI.SNat natParams.length)
    | .param name =>
      match h : natParams.findIdx? (· = name) with
      | .some x => .some <| .param ⟨x, List.findIdx?_lt_of_eq_some h⟩
      | .none => .none
    | .const n => .some <| .const n

  def STyp.toDeBruijn (natParams typParams : List String) : STyp → Option (NKI.STyp natParams.length typParams.length)
    | .param name =>
      match h : typParams.findIdx? (· = name) with
      | .some x => .some <| .param ⟨x, List.findIdx?_lt_of_eq_some h⟩
      | .none => .none
    | .none => .some .none
    | .bool => .some .bool
    | .int => .some .int
    | .float => .some .float
    | .string => .some .string
    | .tuple typs => do
      let typs ← typs.mapM (Nominal.STyp.toDeBruijn natParams typParams)
      return .tuple typs
    | .dtype typ => some (.dtype typ)
    | .tensor shapes typ => do
      let shapes ← shapes.mapM (Nominal.SNat.toDeBruijn natParams)
      return .tensor shapes typ
    | .func dom ran => do
      let dom ← dom.toDeBruijn natParams typParams
      let ran ← ran.toDeBruijn natParams typParams
      return .func dom ran

  def TypParam.nnat (ts : List TypParam) : Nat :=
    (ts.filter (Srt.isNat ∘ TypParam.sort)).length

  def TypParam.ntyp (t : List TypParam) : Nat :=
    (t.filter (Srt.isTyp ∘ TypParam.sort)).length

  /--
  Translate a type definition with concrete names into the De Bruijn representation.

  When there is a name collision, we take the first one in the list.
  -/
  def Typ.toDeBruijn (t : Typ) : Option (NKI.STyp (TypParam.nnat t.params) (TypParam.ntyp t.params)) :=
    match t.typ with
    | .styp typ =>
      let natParams : List String := List.map TypParam.name <| t.params.filter (Srt.isNat ∘ TypParam.sort)
      let typParams : List String := List.map TypParam.name <| t.params.filter (Srt.isTyp ∘ TypParam.sort)
      have hnat : natParams.length = TypParam.nnat t.params := List.length_map _
      have htyp : typParams.length = TypParam.ntyp t.params := List.length_map _
      hnat ▸ htyp ▸ typ.toDeBruijn natParams typParams
    | .snat _ => none

  def SNat.inferBinders (l : List TypParam) : SNat → List TypParam
    | .param name =>
      if name ∈ (l.filter (Srt.isNat ∘ TypParam.sort)).map TypParam.name then
        l
      else
        l.concat ⟨name, .snat⟩
    | .const _ => l

  def STyp.inferBindersAux (l : List TypParam) : STyp → List TypParam
    | .param name =>
      if name ∈ (l.filter (Srt.isTyp ∘ TypParam.sort)).map TypParam.name then
        l
      else
        l.concat ⟨name, .styp⟩
    | .none | .bool | .int | .float | .string | .dtype _ => l
    | .tuple typs => l ++ (typs.map (STyp.inferBindersAux l)).flatten
    | .tensor shapes _ => shapes.foldl SNat.inferBinders l
    | .func dom ran => l ++ dom.inferBindersAux l ++ ran.inferBindersAux l

  /-- Infer the list of type parameters -/
  def STyp.inferBinders (t : STyp) : List TypParam :=
    t.inferBindersAux []

  /-- Infer the De Bruijn indexed version -/
  def STyp.inferDeBruijn (t : STyp) : Option (NKI.STyp (TypParam.nnat t.inferBinders) (TypParam.ntyp t.inferBinders)) :=
    Typ.toDeBruijn ⟨t.inferBinders, .styp t⟩

  /- Parser for type annotations (`pt_` prefix for Py Types) -/

  open Lean Elab Meta

  /- SNat -/
  declare_syntax_cat pt_nat
  syntax ident : pt_nat
  syntax num : pt_nat

  /- DType -/
  declare_syntax_cat pt_dtype
  syntax "bfloat16" : pt_dtype
  syntax "float8e3" : pt_dtype
  syntax "float8e4" : pt_dtype
  syntax "float8e5" : pt_dtype
  syntax "float16" : pt_dtype
  syntax "float32" : pt_dtype
  syntax "float32r" : pt_dtype
  syntax "int8" : pt_dtype
  syntax "int16" : pt_dtype
  syntax "int64" : pt_dtype
  syntax "int32" : pt_dtype
  syntax "uint8" : pt_dtype
  syntax "uint16" : pt_dtype
  syntax "uint32" : pt_dtype
  syntax "uint64" : pt_dtype

  /- STyp -/
  declare_syntax_cat pt_typ

  /- Primitive types -/
  syntax "none" : pt_typ
  syntax "bool" : pt_typ
  syntax "int" : pt_typ
  syntax "float" : pt_typ
  syntax "string" : pt_typ

  /- Type parameter -/
  syntax ident : pt_typ

  /- Tuple syntax -/
  declare_syntax_cat pt_nat_tup
  syntax pt_nat : pt_nat_tup
  syntax pt_nat ", " pt_nat_tup : pt_nat_tup

  declare_syntax_cat pt_typ_tup
  syntax pt_typ : pt_typ_tup
  syntax pt_typ ", " pt_typ_tup : pt_typ_tup

  syntax "tuple[" pt_typ_tup "]" : pt_typ
  syntax "tensor[" pt_dtype ", " "(" pt_nat_tup ")" "]" : pt_typ

  syntax pt_typ " → " pt_typ : pt_typ
  syntax pt_typ " -> " pt_typ : pt_typ

  def elabPtNat : Syntax → MetaM Expr
    | `(pt_nat| $id:ident) => mkAppM ``Nominal.SNat.param #[mkStrLit id.getId.toString]
    | `(pt_nat| $n:num) => mkAppM ``Nominal.SNat.const #[mkNatLit n.getNat]
    | _ => throwUnsupportedSyntax

  def elabPtDtype : Syntax → MetaM Expr
    | `(pt_dtype| bfloat16) => return .const ``KLR.Core.Dtype.bfloat16 []
    | `(pt_dtype| float8e3) => return .const ``KLR.Core.Dtype.float8e3 []
    | `(pt_dtype| float8e4) => return .const ``KLR.Core.Dtype.float8e4 []
    | `(pt_dtype| float8e5) => return .const ``KLR.Core.Dtype.float8e5 []
    | `(pt_dtype| float16) => return .const ``KLR.Core.Dtype.float16 []
    | `(pt_dtype| float32) => return .const ``KLR.Core.Dtype.float32 []
    | `(pt_dtype| float32r) => return .const ``KLR.Core.Dtype.float32r []
    | `(pt_dtype| int8) => return .const ``KLR.Core.Dtype.int8 []
    | `(pt_dtype| int16) => return .const ``KLR.Core.Dtype.int16 []
    | `(pt_dtype| int64) => return .const ``KLR.Core.Dtype.int64 []
    | `(pt_dtype| int32) => return .const ``KLR.Core.Dtype.int32 []
    | `(pt_dtype| uint8) => return .const ``KLR.Core.Dtype.uint8 []
    | `(pt_dtype| uint16) => return .const ``KLR.Core.Dtype.uint16 []
    | `(pt_dtype| uint32) => return .const ``KLR.Core.Dtype.uint32 []
    | `(pt_dtype| uint64) => return .const ``KLR.Core.Dtype.uint64 []
    | _ => throwUnsupportedSyntax

  /- Helpers to make constructing lists easier in elaboration -/
  def SNatNil : List SNat := []
  def SNatCons (n : SNat) (ns : List SNat) : List SNat := n :: ns
  def STypNil : List STyp := []
  def STypCons (t : STyp) (ts : List STyp) : List STyp := t :: ts

  partial def elabPtNatTup : Syntax → MetaM Expr
    | `(pt_nat_tup| $n:pt_nat) => do
      let n ← elabPtNat n
      mkAppM ``SNatCons #[n, .const ``SNatNil []]
    | `(pt_nat_tup| $n:pt_nat, $tup:pt_nat_tup) => do
      let n ← elabPtNat n
      let tup ← elabPtNatTup tup
      mkAppM ``SNatCons #[n, tup]
    | _ => throwUnsupportedSyntax

  mutual

  partial def elabPtTypTup : Syntax → MetaM Expr
    | `(pt_typ_tup| $t:pt_typ) => do
      let t ← elabPtTyp t
      mkAppM ``STypCons #[t, .const ``STypNil []]
    | `(pt_typ_tup| $t:pt_typ, $tup:pt_typ_tup) => do
      let t ← elabPtTyp t
      let tup ← elabPtTypTup tup
      mkAppM ``STypCons #[t, tup]
    | _ => throwUnsupportedSyntax

  partial def elabPtTyp : Syntax → MetaM Expr
    | `(pt_typ| $id:ident) => mkAppM ``Nominal.STyp.param #[mkStrLit id.getId.toString]
    | `(pt_typ| none) => return .const ``Nominal.STyp.none []
    | `(pt_typ| bool) => return .const ``Nominal.STyp.bool []
    | `(pt_typ| int) => return .const ``Nominal.STyp.int []
    | `(pt_typ| float) => return .const ``Nominal.STyp.float []
    | `(pt_typ| string) => return .const ``Nominal.STyp.string []
    | `(pt_typ| tuple[$typs]) => do
      let typs ← elabPtTypTup typs
      mkAppM ``Nominal.STyp.tuple #[typs]
    | `(pt_typ| tensor[$dtype, ($shapes)]) => do
      let dtype ← elabPtDtype dtype
      let shapes ← elabPtNatTup shapes
      mkAppM ``Nominal.STyp.tensor #[shapes, dtype]
    | `(pt_typ| $dom → $ran) | `(pt_typ| $dom -> $ran) => do
      let dom ← elabPtTyp dom
      let ran ← elabPtTyp ran
      mkAppM ``Nominal.STyp.func #[dom, ran]
    | _ => throwUnsupportedSyntax

  end

  elab "pt( " t:pt_typ " )" : term => elabPtTyp t

  #check pt( a )
  #check pt( none )
  #check pt( bool )
  #check pt( int )
  #check pt( float )
  #check pt( string )
  #check pt( tuple[int, t] )
  #check pt( tensor[int32, (m, n, 10)] )
  #check pt( tensor[bfloat16, (m, n, 10)] )
  #check pt( tensor[float8e3, (m, n, 10)] )
  #check pt( tensor[float8e4, (m, n, 10)] )
  #check pt( tensor[float8e5, (m, n, 10)] )
  #check pt( tensor[float16, (m, n, 10)] )
  #check pt( tensor[float32, (m, n, 10)] )
  #check pt( tensor[float32r, (m, n, 10)] )
  #check pt( tensor[int8, (m, n, 10)] )
  #check pt( tensor[int16, (m, n, 10)] )
  #check pt( tensor[int64, (m, n, 10)] )
  #check pt( tensor[int32, (m, n, 10)] )
  #check pt( tensor[uint8, (m, n, 10)] )
  #check pt( tensor[uint16, (m, n, 10)] )
  #check pt( tensor[uint32, (m, n, 10)] )
  #check pt( tensor[uint64, (m, n, 10)] )
  #check pt( int → t → tensor[uint64, (m, n, 10)] )
  #check pt( int -> t -> tensor[uint64, (m, n, 10)] )
  #eval pt( int → t → tensor[uint64, (m, n, 10)] ).inferDeBruijn

end Nominal

end KLR.NKI

namespace TypesExamples

def List.swap (l : List α) (i₁ i₂ : Nat) : List α :=
  if h : i₁ < l.length ∧ i₂ < l.length then
    (l.set i₁ l[i₂]).set i₂ l[i₁]
  else
    l

open KLR NKI

def transpose (nnat ntyp : Nat) (dtype : Core.Dtype) (shapes : List (SNat nnat)) : STyp nnat ntyp :=
  .func (.tensor shapes dtype) (.tensor (List.swap shapes 1 3) dtype)
#eval transpose 0 0 .int32 [.const 1, .const 2, .const 3, .const 4]
#eval transpose 4 1 .int32 [.param 0, .param 1, .param 2, .param 3]

-- `∀ {s1 s2 s3} {t}, tensor[t, s1, s2] → tensor[t, s2, s3] → tensor[t, s1, s3]`
def matmul2d (dtype : Core.Dtype) : STyp 3 0 :=
  .func
    (.tuple [(.tensor [.param 0, .param 1] dtype), .tensor [.param 1, .param 2] dtype])
    (.tensor [.param 0, .param 2] dtype)
#eval matmul2d .bfloat16

-- `∀ {s1 s2 s3} {t}, tensor[t, s1, s2] → tensor[t, s2, s3] → tensor[t, s1, s3]`
def Nominal.matmul2d (dtype : Core.Dtype) : Nominal.Typ :=
  ⟨
    [⟨"s1", .snat⟩, ⟨"s2", .snat⟩, ⟨"s3", .snat⟩, ⟨"t", .styp⟩],
    .styp <|
      .func (.tensor [.param "s1", .param "s2"] dtype) <|
        .func (.tensor [.param "s2", .param "s3"] dtype) (.tensor [.param "s1", .param "s3"] dtype)
  ⟩


end TypesExamples
