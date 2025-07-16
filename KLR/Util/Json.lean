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
import Std

namespace KLR.Util.Json

open Lean(FromJson fromJson? Json ToJson toJson)
open Std(HashMap)

instance : ToJson Float32 where
  toJson f32 := ToJson.toJson f32.toFloat

instance : FromJson Float32 where
  fromJson? j := do
    let f : Float <- FromJson.fromJson? j
    return f.toFloat32

instance : ToJson Int32 where
  toJson i32 := ToJson.toJson i32.toInt

instance : FromJson Int32 where
  fromJson? j := do
    let i : Int <- FromJson.fromJson? j
    return i.toInt32

instance : ToJson UInt32 where
  toJson u := ToJson.toJson u.toNat

instance : FromJson UInt32 where
  fromJson? j := do
    let n : Nat <- FromJson.fromJson? j
    return n.toUInt32


partial def removeNullValues : Json -> Json
| .arr a => .arr (a.map removeNullValues)
| .obj o =>
  let pairs := o.fold (init := []) fun ps k v =>
    if v.isNull then ps else (k, removeNullValues v) :: ps
  Json.mkObj pairs
| j => j

#guard removeNullValues (json% {x: 5, y: null}) == json% {x: 5}
#guard removeNullValues
  (json% [{"output_names":["a_tensor"],"op":"null","name":"a_tensor","is_param":"0","inputs":[],"attrs":null}])
   == (json% [{"output_names":["a_tensor"],"op":"null","name":"a_tensor","is_param":"0","inputs":[]}])

def equalWithoutNullValues (j1 j2 : Json) : Bool :=
  BEq.beq (removeNullValues j1) (removeNullValues j2)

#guard equalWithoutNullValues (json% {x: 5, y: null}) (json%{x: 5, z: null})

def jsonRoundTripEq1 (a : Type) [BEq a] [FromJson a] [ToJson a] (j : Json) : Bool :=
  match fromJson? j with
  | .error _ => false
  | .ok (x : a) => equalWithoutNullValues (toJson x) j

def jsonRoundTripEq [BEq a] [FromJson a] [ToJson a] (x : a) : Bool :=
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

def swapKeys (j : Json) (old new : String) : Json :=
  match j.getObj? with
  | .error _ => j
  | .ok obj => match obj.find compare old with
    | .none => j
    | .some v => (Json.obj (obj.del compare old)).setObjVal! new v

end KLR.Util.Json
