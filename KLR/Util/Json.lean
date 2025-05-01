/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import Std

namespace KLR.Json

open Lean(FromJson fromJson? Json ToJson toJson)
open Std(HashMap)

partial def removeNullValues : Json -> Json
| .arr a => .arr (a.map removeNullValues)
| .obj o =>
  let pairs := o.fold (init := []) fun ps k v =>
    if v.isNull then ps else (k, removeNullValues v) :: ps
  Json.mkObj pairs
| j => j

#guard removeNullValues (json% {x: 5, y: null}) == json% {x: 5}

def equalWithoutNullValues (j1 j2 : Json) : Bool :=
  BEq.beq (removeNullValues j1) (removeNullValues j2)

#guard equalWithoutNullValues (json% {x: 5, y: null}) (json%{x: 5, z: null})

def jsonRoundTripEq1 (a : Type)[BEq a][FromJson a][ToJson a] (j : Json) : Bool :=
  match fromJson? j with
  | .error _ => false
  | .ok (x : a) => equalWithoutNullValues (toJson x) j

def jsonRoundTripEq [BEq a][FromJson a][ToJson a] (x : a) : Bool :=
  let j := toJson x
  let x' := fromJson? j
  match x' with
  | .error _ => false
  | .ok y => x == y && equalWithoutNullValues (toJson y) j

instance HashMapFromJson [FromJson a] : FromJson (HashMap String a) where
  fromJson? j := do
    let node <- j.getObj?
    node.foldM (fun m k v => do
      let v <- fromJson? v
      return m.insert k v
    ) HashMap.emptyWithCapacity

instance HashMapToJson [ToJson a] : ToJson (HashMap String a) where
  toJson m := Json.mkObj $ m.toList.map fun (k, v) => (k, toJson v)

instance HashMapBeq [BEq a] : BEq (HashMap String a) where
  beq m1 m2 := m1.keys.length == m2.keys.length &&
    m1.fold (init := true) fun b k v => b && (match m2.get? k with
     | .none => false
     | .some v' => v == v')

private structure Foo where
  x : Nat
  y : HashMap String Nat
deriving BEq, FromJson, ToJson, Repr

#guard jsonRoundTripEq (Foo.mk 5 (HashMap.ofList [("a", 7), ("b", 16)]))
#guard jsonRoundTripEq1 Foo $ json% { x: 5, y: {"a": 7, "b": 16} }

def NatAsJsonString : Type := Nat deriving BEq, Inhabited, Repr

instance instOfNatNatAsJsonString (n : Nat) : OfNat NatAsJsonString n where
  ofNat := n

instance : FromJson NatAsJsonString where
  fromJson? j := match j.getStr? with
  | .ok s => match s.toNat? with
    | .none => throw s!"Expected string-embedded nat: got {s}"
    | .some n => return n
  | .error msg => throw s!"Expected string-embedded nat: got {j.pretty} with error message {msg}"

instance : ToJson NatAsJsonString where
  toJson n := Json.str n.repr

private structure Bar where
  x : NatAsJsonString
deriving BEq, FromJson, ToJson

#guard jsonRoundTripEq1 Bar $ json%{x: "7"}
#guard toJson (Bar.mk 7) == json%{x: "7"}

end KLR.Json
