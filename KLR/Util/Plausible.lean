/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
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
