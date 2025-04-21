/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

-- SM: Thanks to Claude for most of this code.

namespace SHA256

/-- Initial hash values (first 32 bits of the fractional parts of the square roots of the first 8 primes) -/
private def initHashValues : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-- Round constants (first 32 bits of the fractional parts of the cube roots of the first 64 primes) -/
private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-- Right rotate a 32-bit word -/
private def rightRotate (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Right shift a 32-bit word -/
private def rightShift (x n : UInt32) : UInt32 :=
  x >>> n

/-- SHA-256 functions -/
private def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

private def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def sigma0 (x : UInt32) : UInt32 :=
  rightRotate x 2 ^^^ rightRotate x 13 ^^^ rightRotate x 22

private def sigma1 (x : UInt32) : UInt32 :=
  rightRotate x 6 ^^^ rightRotate x 11 ^^^ rightRotate x 25

private def gamma0 (x : UInt32) : UInt32 :=
  rightRotate x 7 ^^^ rightRotate x 18 ^^^ rightShift x 3

private def gamma1 (x : UInt32) : UInt32 :=
  rightRotate x 17 ^^^ rightRotate x 19 ^^^ rightShift x 10

/-- Convert byte array to UInt32 (big-endian) -/
private def bytesToUInt32 (bytes : Array UInt8) (offset : Nat) : UInt32 :=
  let b0 : UInt32 := bytes[offset]!.toUInt32
  let b1 : UInt32 := bytes[offset + 1]!.toUInt32
  let b2 : UInt32 := bytes[offset + 2]!.toUInt32
  let b3 : UInt32 := bytes[offset + 3]!.toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Convert UInt32 to bytes (big-endian) -/
private def uint32ToBytes (value : UInt32) : Array UInt8 :=
  #[
    (value >>> 24).toUInt8,
    (value >>> 16).toUInt8,
    (value >>> 8).toUInt8,
    value.toUInt8
  ]

/-- Pad message according to SHA-256 specification -/
private def padMessage (message : Array UInt8) : Array UInt8 := Id.run do
  let msgLen := message.size
  let bitLen : UInt64 := UInt64.ofNat (msgLen * 8)

  -- Calculate padding length (need to add 1 + padding + 8 bytes for length)
  let k := (56 - (msgLen + 1) % 64) % 64
  let paddingSize := 1 + k + 8

  -- Create padded message
  let mut padded := Array.mkArray (msgLen + paddingSize) 0

  -- Copy original message
  for i in [:msgLen] do
    padded := padded.set! i message[i]!

  -- Add '1' bit followed by zeros
  padded := padded.set! msgLen 0x80

  -- Add message length as 64-bit big-endian integer
  for i in [0:8] do
    let shift := (7 - i) * 8
    padded := padded.set! (msgLen + 1 + k + i) ((bitLen >>> shift.toUInt64) &&& 0xFF).toUInt8

  return padded

/-- Process a 64-byte block -/
private def processBlock (block : Array UInt8) (hash : Array UInt32) : Array UInt32 := Id.run do
  -- Prepare message schedule
  let mut w := Array.mkArray 64 (0 : UInt32)

  -- Copy block into first 16 words (32-bit big-endian integers)
  for i in [0:16] do
    w := w.set! i (bytesToUInt32 block (i * 4))

  -- Extend the first 16 words into the remaining 48 words
  for i in [16:64] do
    let s0 := gamma0 w[i-15]!
    let s1 := gamma1 w[i-2]!
    let newWord := w[i-16]! + s0 + w[i-7]! + s1
    w := w.set! i newWord

  -- Initialize working variables
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!

  -- Main loop
  for i in [0:64] do
    let S1 := sigma1 e
    let ch := ch e f g
    let temp1 := h + S1 + ch + roundConstants[i]! + w[i]!
    let S0 := sigma0 a
    let maj := maj a b c
    let temp2 := S0 + maj

    h := g
    g := f
    f := e
    e := d + temp1
    d := c
    c := b
    b := a
    a := temp1 + temp2

  -- Update hash values
  let mut newHash := hash
  newHash := newHash.set! 0 (newHash[0]! + a)
  newHash := newHash.set! 1 (newHash[1]! + b)
  newHash := newHash.set! 2 (newHash[2]! + c)
  newHash := newHash.set! 3 (newHash[3]! + d)
  newHash := newHash.set! 4 (newHash[4]! + e)
  newHash := newHash.set! 5 (newHash[5]! + f)
  newHash := newHash.set! 6 (newHash[6]! + g)
  newHash := newHash.set! 7 (newHash[7]! + h)

  return newHash

/-- Compute SHA-256 hash of a message -/
private def hash (message : Array UInt8) : Array UInt8 := Id.run do
  let padded := padMessage message
  let mut hashValues := initHashValues

  -- Process message in 64-byte blocks
  for blockStart in List.range (padded.size / 64) do
    let blockOffset := blockStart * 64
    let mut block := Array.mkArray 64 (0 : UInt8)

    -- Extract current block
    for i in [0:64] do
      block := block.set! i padded[blockOffset + i]!

    -- Process block
    hashValues := processBlock block hashValues

  -- Convert hash values to bytes
  let mut result := Array.mkArray 32 (0 : UInt8)
  for i in [0:8] do
    let bytes := uint32ToBytes hashValues[i]!
    for j in [0:4] do
      result := result.set! (i * 4 + j) bytes[j]!

  return result

/-- Convert hash to hex string -/
private def toHexString (hash : Array UInt8) : String := Id.run do
  let hexChars := "0123456789abcdef".toList
  let mut result := ""

  for b in hash do
    let hi := (b >>> 4).toNat
    let lo := (b &&& 0xF).toNat
    result := result.push (hexChars[hi]!)
    result := result.push (hexChars[lo]!)

  return result

/-- Compute SHA-256 hash of a string -/
private def hashString (s : String) : String := Id.run do
  let bytes := s.toUTF8
  let hashBytes := hash bytes.data
  return toHexString hashBytes

-- echo -n 'Hello, world!' | sha256sum
-- 315f5bdb76d078c43b8ac0064e4a0164612b1fce77c869345bfc94c75894edd3
#guard hashString "Hello, world!" == "315f5bdb76d078c43b8ac0064e4a0164612b1fce77c869345bfc94c75894edd3"

-- $ echo -n '' | sha256sum
-- e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
#guard hashString "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

-- $echo -n '🏎️' | sha256sum
-- 02920c55aca4f57f5c02ee91dc2f25293ad91ef899684d977a2eeb666e89cbfc
#guard hashString "🏎️" == "02920c55aca4f57f5c02ee91dc2f25293ad91ef899684d977a2eeb666e89cbfc"

end SHA256
