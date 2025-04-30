/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Plausible

namespace KLR.Util

def _root_.ByteArray.ofUInt32LE (val : UInt32) : ByteArray := ByteArray.mk #[
  (val >>>  0).toUInt8,
  (val >>>  8).toUInt8,
  (val >>> 16).toUInt8,
  (val >>> 24).toUInt8
]

def _root_.ByteArray.ofUInt64LE (val : UInt64) : ByteArray := ByteArray.mk #[
  (val >>>  0).toUInt8,
  (val >>>  8).toUInt8,
  (val >>> 16).toUInt8,
  (val >>> 24).toUInt8,
  (val >>> 32).toUInt8,
  (val >>> 40).toUInt8,
  (val >>> 48).toUInt8,
  (val >>> 56).toUInt8
]

def _root_.ByteArray.readUInt32 (arr : ByteArray) (offset : Nat) : UInt32 :=
  if arr.size < offset + 4 then 0 else
  let b0 := arr[offset]!.toUInt32
  let b1 := arr[offset + 1]!.toUInt32
  let b2 := arr[offset + 2]!.toUInt32
  let b3 := arr[offset + 3]!.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

def _root_.ByteArray.readUInt64 (arr : ByteArray) (offset : Nat) : UInt64 :=
  if arr.size < offset + 8 then 0 else
  let b0 := arr[offset]!.toUInt64
  let b1 := arr[offset + 1]!.toUInt64
  let b2 := arr[offset + 2]!.toUInt64
  let b3 := arr[offset + 3]!.toUInt64
  let b4 := arr[offset + 4]!.toUInt64
  let b5 := arr[offset + 5]!.toUInt64
  let b6 := arr[offset + 6]!.toUInt64
  let b7 := arr[offset + 7]!.toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

section Test
open Plausible

private def cfg : Plausible.Configuration := {}

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (v : UInt32) :
  (ByteArray.ofUInt32LE v).readUInt32 0 == v := by
  plausible (config := cfg)

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (v : UInt64) :
  (ByteArray.ofUInt64LE v).readUInt64 0 == v := by
  plausible (config := cfg)

end Test

end KLR.Util
