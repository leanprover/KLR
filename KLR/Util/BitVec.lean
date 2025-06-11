/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Claude
-/
import Plausible
import Util.Common

namespace KLR.Util.BitVec

open Plausible(Gen)

/-- Convert a character to its ASCII/UTF-8 value as a BitVec 8 -/
private def charToBitVec8 (c : Char) : BitVec 8 :=
  BitVec.ofNat 8 c.toNat

/-- Convert a BitVec 8 to a character -/
private def bitVec8ToChar (bv : BitVec 8) : Char :=
  Char.ofNat bv.toNat

/-- Convert a list of BitVec 8 values to a string -/
private def bitVecListToString (bvList : List (BitVec 8)) : String :=
  String.mk (bvList.map bitVec8ToChar)

private def isAsciiChar (c : Char) : Bool := c.toNat < 128

private def isAscii (s : String) : Bool := s.data.all isAsciiChar

/-- Convert a string to a single BitVec of appropriate size in little-endian order -/
def asciiStringToBitVec (n : Nat) (s : String) : Err (BitVec n) := do
  if n % 8 != 0 then throw "size should be divisible by 8" else
  if !isAscii s then throw "not an ascii string" else
  if n < s.length * 8 then throw "string is too long for storage" else
  let mut bytes : BitVec n := 0
  let mut i := 0
  for byte in s.toList.map charToBitVec8 do
    let shiftAmount := i * 8
    let shiftedB := BitVec.zeroExtend n byte
    let shiftedVal := shiftedB <<< shiftAmount
    i := i + 1
    bytes := bytes ||| shiftedVal
  return bytes

/-- Convert a BitVec back to a string, assuming little-endian byte order and known string length -/
def bitVecToAsciiString {n : Nat} (bv : BitVec n) : Err String := do
  if n % 8 != 0 then throw "size should be divisible by 8" else
  let mut chars := []
  for i in [0:n/8] do
    let shiftAmount := i * 8
    let mask := BitVec.zeroExtend n (BitVec.ofNat 8 0xFF)
    let shiftedMask := mask <<< shiftAmount
    let extractedByte := (bv &&& shiftedMask) >>> shiftAmount
    chars := BitVec.truncate 8 extractedByte :: chars
  return bitVecListToString chars.reverse

private def smallNatGen : Gen Nat := Plausible.Gen.choose Nat 0 128 (by omega)
private def asciiCharGen : Gen Char := smallNatGen.bind fun n => return Char.ofNat n
private def asciiStringGen : Gen String := do
  let l <- Plausible.Gen.listOf asciiCharGen
  return String.mk l

private def roundTrip (n : Nat) (s : String) : Err String := do
  bitVecToAsciiString (<- asciiStringToBitVec n s)

private def ok (n : Nat) (s : String) : Bool := match roundTrip n s with
| .error _ => false
| .ok s' => s == s'

#guard roundTrip 32 "sean" == .ok "sean"
#guard roundTrip 24 "sean" == .error "string is too long for storage"
#guard roundTrip 25 "sean" == .error "size should be divisible by 8"
#guard roundTrip 24 "🏎️" == .error "not an ascii string"
-- We 0-pad to fill the gaps
#guard roundTrip 40 "sean" == .ok "sean\x00"
#guard roundTrip 48 "sean" == .ok "sean\x00\x00"

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (s : String) : ok (s.length * 8) s := by plausible

end KLR.Util.BitVec
