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

namespace KLR.NKI.Typed

open KLR.Py (Span Ident FileInfo)

inductive ContextElem
  | forall       (name : Ident)
  | var          (name : Ident) (typ : Typ)
  | exists       (name : Ident)
  | existsSolved (name : Ident) (typ : Typ)
  | marker       (name : Ident)

def ContextElem.toString : ContextElem → String
  | .forall       name     => s!"∀ {name}"
  | .var          name typ => s!"{name} : {typ}"
  | .exists       name     => s!"?{name}"
  | .existsSolved name typ => s!"?{name} = {typ}"
  | .marker       name     => s!"▶{name}"

instance : ToString ContextElem := ⟨ContextElem.toString⟩

def ContextElem.beq : ContextElem → ContextElem → Bool
  | .forall x, .forall y
  | .var x _, .var y _
  | .exists x, .exists y
  | .existsSolved x _, .existsSolved y _
  | .marker x, .marker y => x == y
  | _, _ => false

instance : BEq ContextElem := ⟨ContextElem.beq⟩

def ContextElem.isIncomplete : ContextElem → Bool
  | .exists _ => true
  | _ => false

abbrev Context := Array ContextElem

def Context.existentials (Γ : Context) : Array Ident := Id.run do
  let mut res := #[]
  for ce in Γ do
    match ce with
    | .exists name
    | .existsSolved name _ =>
      res := res.push name
    | _ => continue
  return res

def Context.unsolved (Γ : Context) : Array Ident := Id.run do
  let mut res := #[]
  for ce in Γ do
    match ce with
    | .exists name => res := res.push name
    | _ => continue
  return res

def Context.vars (Γ : Context) : Array Ident := Id.run do
  let mut res := #[]
  for ce in Γ do
    match ce with
    | .var name _ => res := res.push name
    | _ => continue
  return res

def Context.foralls (Γ : Context) : Array Ident := Id.run do
  let mut res := #[]
  for ce in Γ do
    match ce with
    | .forall name => res := res.push name
    | _ => continue
  return res

def Context.markers (Γ : Context) : Array Ident := Id.run do
  let mut res := #[]
  for ce in Γ do
    match ce with
    | .marker name => res := res.push name
    | _ => continue
  return res

def Context.isIncomplete (Γ : Context) : Bool :=
  Γ.foldl (fun ic e => ic || e.isIncomplete) false

def Context.dropMarker (Γ : Context) (m : ContextElem) : Context :=
  Γ.takeWhile (not ∘ ContextElem.beq m)

def Context.breakMarker (Γ : Context) (m : ContextElem) : Option (Context × Context) :=
  Γ.findIdx? (ContextElem.beq m) |> .map fun idx =>
  (Γ[:idx].toArray, Γ[idx+1:].toArray)

def Context.ordered (Γ : Context) (a b : Ident) : Bool :=
  (Γ.dropMarker (.exists b)).existentials.contains a

def Context.insertAt (Γ : Context) (ce : ContextElem) (m : Context) : Option Context :=
  if !ce.isIncomplete then none else
  if let some (l, r) := Γ.breakMarker ce then
    some <| l ++ m ++ r
  else
    none

def Context.findSolved (Γ : Context) (var : Ident) : Option Typ := Id.run do
  for ce in Γ do
    match ce with
    | .existsSolved var' t =>
      if var == var' then
        return t
    | _ => continue
  return none

def Context.findVarType (Γ : Context) (name : Ident) : Option Typ := Id.run do
  for ce in Γ.reverse do
    match ce with
    | .var name' t =>
      if name == name' then
        return t
    | _ => continue
  return none

def Context.apply (Γ : Context) (t : Typ) : Typ :=
  match t with
  | .var _ _                => t
  | .evar _ name            => (Γ.findSolved name).getD t
  | .forall span names body => .forall span names (Γ.apply body)
  | .prim _ _               => t
  | .func span params ret   => .func span (params.map Γ.apply) (Γ.apply ret)
  | .size _ _               => t
  | .shape span dims        => .shape span (dims.map Γ.apply)
  | .tuple span typs        => .tuple span (typs.map Γ.apply)
  | .list span typ          => .list span (Γ.apply typ)
  | .tensor span sh dt      => .tensor span (Γ.apply sh) (Γ.apply dt)
  | .iter span typ          => .iter span (Γ.apply typ)
  | .sizeAdd span x y       => .sizeAdd span (Γ.apply x) (Γ.apply y)
  | .shapeAppend span s1 s2 => .shapeAppend span (Γ.apply s1) (Γ.apply s2)

def Context.upgradeToFloat (Γ : Context) (α : Ident) : Context :=
  Γ.map fun ce =>
    match ce with
    | .existsSolved β (.prim span (.numeric .int)) =>
      if α == β then
        .existsSolved β (.prim span (.numeric .float))
      else
        ce
    | _ => ce
