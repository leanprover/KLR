/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

import Plausible

namespace Util
namespace Base64

/-- The standard Base64 encoding alphabet -/
private def encodeTable : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".data.toArray

/-- The padding character used in Base64 encoding -/
private def paddingChar : Char := '='

/-- Create a decode table mapping each Base64 character to its 6-bit value -/
private def decodeTable : Array UInt8 := Id.run do
  let mut table := Array.mkArray 256 0
  let mut i := 0
  for c in encodeTable do
    table := table.set! c.toNat i
    i := i + 1
  table

/--
  Encode a ByteArray to a Base64 string.

  This function takes a ByteArray and converts it to a Base64-encoded string
  according to the standard Base64 encoding (RFC 4648).
-/
def encode (input : ByteArray) : String := Id.run do
if input.isEmpty then "" else
let mut result := ""
let len := input.size
let fullGroups := len / 3
let remainingBytes := len % 3
-- Process full 3-byte groups
for i in [0:fullGroups] do
  let idx := i * 3
  let b1 := input.get! idx
  let b2 := input.get! (idx + 1)
  let b3 := input.get! (idx + 2)
  -- Convert 3 bytes (24 bits) to 4 Base64 characters (6 bits each)
  let c1 := encodeTable[(b1 >>> 2).toNat]!
  let c2 := encodeTable[((b1 &&& 0x03) <<< 4 ||| (b2 >>> 4)).toNat]!
  let c3 := encodeTable[((b2 &&& 0x0F) <<< 2 ||| (b3 >>> 6)).toNat]!
  let c4 := encodeTable[(b3 &&& 0x3F).toNat]!
  result := result.push c1 |>.push c2 |>.push c3 |>.push c4
-- Handle remaining bytes with padding
if remainingBytes == 1 then
  let b1 := input.get! (fullGroups * 3)
  let c1 := encodeTable[(b1 >>> 2).toNat]!
  let c2 := encodeTable[((b1 &&& 0x03) <<< 4).toNat]!
  result := result.push c1 |>.push c2 |>.push paddingChar |>.push paddingChar
else if remainingBytes == 2 then
  let b1 := input.get! (fullGroups * 3)
  let b2 := input.get! (fullGroups * 3 + 1)
  let c1 := encodeTable[(b1 >>> 2).toNat]!
  let c2 := encodeTable[((b1 &&& 0x03) <<< 4 ||| (b2 >>> 4)).toNat]!
  let c3 := encodeTable[((b2 &&& 0x0F) <<< 2).toNat]!
  result := result.push c1 |>.push c2 |>.push c3 |>.push paddingChar
result

/--
  Decode a Base64 string to a ByteArray.

  This function takes a Base64-encoded string and converts it back to the original
  binary data as a ByteArray. It handles padding and ignores invalid characters.
-/
def decode (input : String) : Option ByteArray := Id.run do
  -- Remove whitespace and other non-Base64 characters
  let cleanInput := input.foldl (fun acc c =>
    if encodeTable.contains c || c == paddingChar then acc.push c else acc) ""

  if cleanInput.isEmpty then return ByteArray.empty else
  -- Check if the length is valid (must be a multiple of 4)
  if cleanInput.length % 4 != 0 then none else

  -- Calculate the expected output size based on padding
  let paddingCount := cleanInput.data.count paddingChar
  let outputSize := cleanInput.length / 4 * 3 - paddingCount

  let mut result := ByteArray.mkEmpty outputSize
  let mut buffer : UInt32 := 0
  let mut bufferBits : UInt32 := 0

  for c in cleanInput.data do
    if c == paddingChar then continue
    -- Get the 6-bit value for this character
    let value := decodeTable[c.toNat]!
    if 64 <= value then return none
    -- Add 6 bits to the buffer
    buffer := (buffer <<< 6) ||| value.toUInt32
    bufferBits := bufferBits + 6
    -- If we have at least 8 bits, we can output a byte
    if bufferBits >= 8 then
      bufferBits := bufferBits - 8
      -- Extract the top 8 bits
      let byte := (buffer >>> bufferBits) &&& 0xFF
      result := result.push byte.toUInt8
  return result

/--
  Encode a String to a Base64 string by first converting it to UTF-8 bytes.
-/
def encodeString (input : String) : String :=
  encode (input.toUTF8)

/--
  Decode a Base64 string to a String by interpreting the bytes as UTF-8.
  Returns none if the Base64 string is invalid or the resulting bytes are not valid UTF-8.
-/
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

#guard encodeString "plausible" == "cGxhdXNpYmxl"

#guard
  let b := ByteArray.mk #[1]
  let e := encode b
  let d := decode e
  d == some b

#guard
  let s := "klr-is-the-best"
  let e := encodeString s
  let d := decodeString e
  s == some d

private def plausibleDefaultConfig : Plausible.Configuration := {}

/-
This suppresses messages from Plausible on the commandline when building, such as
    info: ././././TensorLib/Common.lean:37:0: Unable to find a counter-example
If you want to see the counterexample in the IDE, you need to remove the configuration argument,
but remember to add it back once you've fixed the bug.
-/
private def cfg : Plausible.Configuration := plausibleDefaultConfig -- { plausibleDefaultConfig with quiet := true }

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (arr : ByteArray) :
  let s := encode arr
  let v := decode s
  some arr == v := by
  plausible (config := cfg)

end Test
end Base64
end Util
