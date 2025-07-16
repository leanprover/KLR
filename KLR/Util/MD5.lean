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

import TensorLib.ByteArray -- For BEq
import Util.Hex

namespace KLR.Util.MD5

open TensorLib(get!)

/-- Initial state values for MD5 algorithm -/
private def initState : Array UInt32 := #[
  0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476
]

/-- Per-round shift amounts -/
private def shifts : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
]

/-- Precomputed constants for MD5 algorithm -/
private def constants : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
]

/-- Left rotate a 32-bit unsigned integer by specified number of bits -/
private def leftRotate (x : UInt32) (c : UInt32) : UInt32 :=
  (x <<< c) ||| (x >>> (32 - c))

/-- Convert 4 bytes to UInt32 (little-endian) -/
private def bytesToUInt32 (bytes : ByteArray) (offset : Nat) : UInt32 :=
  let b0 : UInt32 := bytes.get! offset |>.toUInt32
  let b1 : UInt32 := bytes.get! (offset + 1) |>.toUInt32
  let b2 : UInt32 := bytes.get! (offset + 2) |>.toUInt32
  let b3 : UInt32 := bytes.get! (offset + 3) |>.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Process a 64-byte chunk of data -/
private def processChunk (state : Array UInt32) (chunk : ByteArray) : Array UInt32 := Id.run do
  -- Convert chunk to 16 UInt32 values (M array)
  let mut M : Array UInt32 := Array.replicate 16 0
  for i in [0:16] do
    M := M.set! i (bytesToUInt32 chunk (i * 4))

  -- Initialize working variables
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!

  -- Main loop
  for i in [0:64] do
    let mut f : UInt32 := 0
    let mut g : Nat := 0

    if i < 16 then
      f := (b &&& c) ||| ((~~~b) &&& d)
      g := i
    else if i < 32 then
      f := (d &&& b) ||| ((~~~d) &&& c)
      g := (5 * i + 1) % 16
    else if i < 48 then
      f := b ^^^ c ^^^ d
      g := (3 * i + 5) % 16
    else
      f := c ^^^ (b ||| (~~~d))
      g := (7 * i) % 16

    let temp := d
    d := c
    c := b
    b := b + leftRotate (a + f + constants[i]! + M[g]!) (shifts[i]!)
    a := temp

  -- Add result to state
  #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d]

/-- Pad message according to MD5 specification -/
private def padMessage (message : ByteArray) : ByteArray := Id.run do
  let origLength := message.size
  let bitLength : UInt64 := (origLength.toUInt64 * 8)

  -- Calculate how many bytes we need to add
  let mut padLength := 64 - (origLength % 64)
  if padLength < 9 then
    padLength := padLength + 64

  -- Create new byte array with padding
  let mut result := ByteArray.emptyWithCapacity (origLength + padLength)

  -- Copy original message
  for i in [0:origLength] do
    result := result.push (message.get! i)

  -- Add padding byte 0x80 followed by zeros
  result := result.push 0x80
  for _i in [1:padLength-8] do
    result := result.push 0

  -- Add original length in bits as 64-bit little-endian integer
  for i in [0:8] do
    let shift : UInt64 := (i * 8).toUInt64
    let b := ((bitLength >>> shift) &&& 0xFF).toUInt8
    result := result.push b

  result

/-- Convert UInt32 to bytes in little-endian order -/
private def uint32ToBytes (x : UInt32) : Array UInt8 :=
  #[
    (x &&& 0xFF).toUInt8,
    ((x >>> 8) &&& 0xFF).toUInt8,
    ((x >>> 16) &&& 0xFF).toUInt8,
    ((x >>> 24) &&& 0xFF).toUInt8
  ]

/-- Compute MD5 hash of a ByteArray -/
def md5 (data : ByteArray) : ByteArray := Id.run do
  let padded := padMessage data

  -- Initialize hash state
  let mut state := initState

  -- Process message in 64-byte chunks
  let numChunks := padded.size / 64
  for i in [0:numChunks] do
    let chunkStart := i * 64
    let chunk := padded.extract chunkStart 64
    state := processChunk state chunk

  -- Convert hash to hex string
  let mut result := #[]
  for i in [0:4] do
    let bytes := uint32ToBytes state[i]!
    for b in bytes do
      result := result.push b

  ⟨ result ⟩

def md5String (s : String) : String := Hex.encode (md5 s.toUTF8)

#guard md5String "" == "d41d8cd98f00b204e9800998ecf8427e"
#guard md5String "The quick brown fox jumps over the lazy dog" == "9e107d9d372bb6826bd81d3542a419d6"
#guard md5 ByteArray.empty == get! (Hex.decode "d41d8cd98f00b204e9800998ecf8427e")
#guard (md5 ByteArray.empty).size == 16

end KLR.Util.MD5
