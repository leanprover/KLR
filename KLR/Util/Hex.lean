/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import Plausible

namespace KLR.Util.Hex

def encode (input : ByteArray) : String := Id.run do
  let hexChars := "0123456789abcdef".toList
  let mut result := ""
  for b in input do
    let hi := (b >>> 4).toNat
    let lo := (b &&& 0xF).toNat
    result := result.push (hexChars[hi]!)
    result := result.push (hexChars[lo]!)
  return result

private def hexCharToNibble (c : Char) : Option UInt8 :=
  let u10 : UInt8 := 10
  if '0' ≤ c && c ≤ '9' then c.toUInt8 - '0'.toUInt8
  else if 'a' ≤ c && c ≤ 'f' then c.toUInt8 - 'a'.toUInt8 + u10
  else if 'A' ≤ c && c ≤ 'F' then c.toUInt8 - 'A'.toUInt8 + u10
  else none

private def hexCharToUInt8 (high : Char) (low : Char) : Option UInt8 := do
  let highNibble ← hexCharToNibble high
  let lowNibble ← hexCharToNibble low
  return (highNibble <<< 4) + lowNibble

def decode (s : String) : Option ByteArray := Id.run do
  let rec split : List Char -> List (Char × Char)
  | [] | [_] => []
  | x0 :: x1 :: xs => (x0, x1) :: split xs
  let s := if s.length % 2 == 0 then s else "0" ++ s
  let mut buf := ByteArray.emptyWithCapacity (s.length / 2)
  for (hi, lo) in split s.data do
    match hexCharToUInt8 hi lo with
    | none => return none
    | some n => buf := buf.push n
  return buf

def encodeString (input : String) : String := encode input.toUTF8

def decodeString (input : String) : Option String :=
  match decode input with
  | none => none
  | some bytes => String.fromUTF8? bytes

section Test

open Plausible

private local instance : Repr ByteArray where
  reprPrec arr n := reprPrec arr.data n

private local instance : BEq ByteArray where
  beq (x y : ByteArray) := x.data == y.data

private local instance : Shrinkable ByteArray where

private local instance : SampleableExt ByteArray :=
  SampleableExt.mkSelfContained do
    let data ← SampleableExt.interpSample (Array UInt8)
    return ByteArray.mk data

#guard encodeString "plausible" == "706c61757369626c65"

#guard
  let b := ByteArray.mk #[1]
  decode (encode b) == b

#guard
  let s := "klr-is-the-best"
  let e := encodeString s
  let d := decodeString e
  s == some d

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (arr : ByteArray) :
  let s := encode arr
  let v := decode s
  some arr == v := by plausible

end Test

end KLR.Util.Hex
