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

import Plausible

/-
Common instances for Plausible
-/
namespace KLR.Util.Plausible

instance : Plausible.Shrinkable Int8 := ⟨ fun _ => [] ⟩
instance : Plausible.SampleableExt Int8 :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt8.size (Nat.zero_lt_succ _)
    return x.val.toInt8

instance : Plausible.Shrinkable Int16 := ⟨ fun _ => [] ⟩
instance : Plausible.SampleableExt Int16 :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt16.size (Nat.zero_lt_succ _)
    return x.val.toInt16

instance : Plausible.Shrinkable Int32 := ⟨ fun _ => [] ⟩
instance : Plausible.SampleableExt Int32 :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt32.size (Nat.zero_lt_succ _)
    return x.val.toInt32

instance : Plausible.Shrinkable Int64 := ⟨ fun _ => [] ⟩
instance : Plausible.SampleableExt Int64 :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt64.size (Nat.zero_lt_succ _)
    return x.val.toInt64


instance : Plausible.Shrinkable Float32 := ⟨ fun _ => [] ⟩
instance : Plausible.SampleableExt Float32 :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt32.size (Nat.zero_lt_succ _)
    return Float32.ofBits x.val.toUInt32

instance : Plausible.Shrinkable Float := ⟨ fun _ => [] ⟩
instance : Plausible.SampleableExt Float :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt64.size (Nat.zero_lt_succ _)
    return Float.ofBits x.val.toUInt64
