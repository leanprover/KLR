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

import KLR.Util
import Plausible
import TensorLib  -- for all the nice conversion functions

/-
# Encoding and Decoding of Basic CBOR values

https://cbor.io
https://www.rfc-editor.org/rfc/rfc8949.html
-/

namespace KLR.Serde

open TensorLib(toBEByteArray)

class ToCBOR (a : Type u) where
  toCBOR : a -> ByteArray

export ToCBOR (toCBOR)

class FromCBOR (a : Type u) where
  parse (arr : ByteArray) : Err (Nat × a)

open FromCBOR (parse)

-- This is used by the derived instances
def parseCBOR' [FromCBOR a] (arr : ByteArray) (size : Nat) : Err (ByteArray × Nat × a) :=
  (parse arr).map fun (sz, x) =>
    (.mk (arr.data.drop sz), sz + size, x)

def parseCBOR [FromCBOR a] (arr : ByteArray) : Err (ByteArray × a) :=
  (parse arr).map fun (sz, x) =>
    (.mk (arr.data.drop sz), x)

def fromCBOR [FromCBOR a] (arr : ByteArray) : Err a :=
  (parse arr).map Prod.snd


-- Often we want to modify an encoding by adding some additional bits to the type tag
private def adjustTag (bit : UInt8) (a : ByteArray) : ByteArray :=
  .mk $ a.data.set! 0 (a.data[0]! ||| bit)

-- Prepend a tag byte to an existing ByteAarray
private def withTag (tag : UInt8) (arr : ByteArray) : ByteArray :=
  let res := ByteArray.emptyWithCapacity (arr.size + 1)
  let res := res.push tag
  ByteArray.copySlice arr 0 res 1 arr.size (exact := true)

-- Parse a value and then apply a transformation
private def parseMap (a : Type) [FromCBOR a] (f : a -> b) (arr : ByteArray) : Err (Nat × b) := do
  let (sz, x) <- parse arr
  return (sz, f x)

/-
For testing with Plausible we override the Float instances
to avoid NaN in these because they cause false negatives on
round-trip tests.
-/
local instance : Plausible.SampleableExt Float32 :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt32.size (Nat.zero_lt_succ _)
    let f := Float32.ofBits x.val.toUInt32
    return if f.isNaN then 0.0 else f

local instance : Plausible.SampleableExt Float :=
  Plausible.SampleableExt.mkSelfContained do
    let x <- Plausible.Gen.chooseNatLt 0 UInt64.size (Nat.zero_lt_succ _)
    let f := Float.ofBits x.val.toUInt64
    return if f.isNaN then 0.0 else f

def roundtrip [BEq a] [ToCBOR a] [FromCBOR a] (x : a) : Bool :=
  match fromCBOR (toCBOR x) with
  | .error _ => false
  | .ok y => x == y

/-
# Booleans
-/

instance : ToCBOR Bool where
  toCBOR
    | false => .mk #[0xf4]
    | true  => .mk #[0xf5]

instance : FromCBOR Bool where
  parse arr := do
    if h:arr.size > 0 then
      match arr[0]'h with
      | 0xf4 => return (1, false)
      | 0xf5 => return (1, true)
      | _ => throw "expecting boolean"
    else throw "expecting Boolean"

-- Only two cases, so no plausible for this test
#eval do
  if roundtrip true == false then
    throwError "CBOR Bool mismatch: true"
  if roundtrip false == false then
    throwError "CBOR Bool mismatch: false"

-- ... or we could also just prove the theorem
-- With some automation, may be able to prove all these theorems
theorem rt_bool (b : Bool) :
  .ok b = fromCBOR (toCBOR b) := by
    unfold toCBOR fromCBOR
    unfold parse
    unfold instToCBORBool instFromCBORBool
    unfold ByteArray.size Except.map Prod.snd
    unfold getElem
    unfold ByteArray.instGetElemNatUInt8LtSize
    unfold ByteArray.get
    unfold pure Applicative.toPure Monad.toApplicative
    unfold Except.instMonad
    unfold Except.pure
    induction b <;> simp
    done

/-
# 8-bit integers
-/

instance : ToCBOR UInt8 where
  toCBOR x :=
    if x < 0x18 then .mk #[x]
    else .mk #[0x18, x]

instance : ToCBOR Int8 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt8
    else adjustTag 0x20 (toCBOR (x.abs.toUInt8 - 1))

/-
This is a common pattern for the unsigned integers. If the value is less than
our tag, then we try the next smallest integer type. Otherwise, we remove the
tag and try to parse the value.
-/
private def fromFixed (arr : ByteArray) (tag : UInt8) (next f : ByteArray -> Err a) : Err a :=
  if h:arr.size > 0 then
    let b0 := arr[0]'h
    if b0 < tag then
      next arr
    else if b0 == tag then
      f (arr.drop 1)
    else throw s!"expecting unsigned integer (got tag {tag})"
  else throw "expecting unsigned integer: got EOF"

instance : FromCBOR UInt8 where
  parse arr := do
    fromFixed arr 0x18
      fun arr => return (1, arr[0]!) -- fromFixed will have checked this is OK
      fun arr =>
        if h:arr.size > 0 then return (2, arr[0])
        else throw "expecting UInt8"

/-
This is a common pattern: many encodings use unsigned integers with a different
major code (upper three bits). To handle this, we clear the upper three bits
(major code) and try to parse the result, and return the major code, and value.
Note, because we ara clearing the major code, the only types which will work are
the unsigned integer types.
-/
private def parseUInt (a : Type) [FromCBOR a] (arr : ByteArray) : Err (UInt8 × Nat × a) := do
  if h:arr.size > 0 then
    let b0 := arr[0]'h
    let major := b0 &&& 0xe0 -- top 3 bits
    let arr := arr.set 0 (b0 &&& 0x1f) -- clear top 3 bits
    let (sz, x) <- @parse a _ arr  -- try to parse at type a
    return (major, sz, x)
  throw "expecting integer"

/-
The encoding of signed and unsigned is the same except for the major type,
which is 1 for signed instead of 0. Parse the unsigned number, check the major
code and flip the sign if needed.
-/
private def checkSign (a : Type) [FromCBOR a] (arr : ByteArray) : Err (Bool × Nat × a) := do
  let (major, sz, x) <- parseUInt a arr
  if major == 0x00 then
    return (false, sz, x)
  if major == 0x20 then
    return (true, sz, x)
  throw "expecting integer"

instance : FromCBOR Int8 where
  parse arr := do
    let (signed, sz, x) <- checkSign UInt8 arr
    if signed
    then return (sz, (x+1).toInt8.neg)
    else return (sz, x.toInt8)

-- Test vectors from RFC
#guard (toCBOR (0 : UInt8)).data == #[0]
#guard (toCBOR (23 : UInt8)).data == #[23]
#guard (toCBOR (24 : UInt8)).data == #[0x18, 24]
#guard (toCBOR (100 : UInt8)).data == #[0x18, 0x64]
#guard (toCBOR (255 : UInt8)).data == #[0x18, 255]

#guard (toCBOR (-1 : Int8)).data == #[0x20]
#guard (toCBOR (-10 : Int8)).data == #[0x29]
#guard (toCBOR (-100 : Int8)).data == #[0x38, 0x63]
#guard (toCBOR Int8.maxValue).data == #[0x18, 0x7f]
#guard (toCBOR Int8.minValue).data == #[0x38, 0x7f]

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : UInt8) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Int8) :
    roundtrip x == true := by plausible

/-
# 16-bit integers
-/

instance : ToCBOR UInt16 where
  toCBOR x :=
    if x.toNat < UInt8.size
    then toCBOR x.toUInt8
    else withTag 0x19 (toBEByteArray x)

instance : ToCBOR Int16 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt16
    else adjustTag 0x20 (toCBOR (x.abs.toUInt16 - 1))

instance : FromCBOR UInt16 where
  parse arr :=
    fromFixed arr 0x19
      (parseMap UInt8 fun x => x.toUInt16)
      fun arr => return (3, <- (arr.take 2).toUInt16BE)

instance : FromCBOR Int16 where
  parse arr := do
    let (signed, sz, x) <- checkSign UInt16 arr
    if signed
    then return (sz, (x+1).toInt16.neg)
    else return (sz, x.toInt16)

-- Test vectors from RFC
#guard (toCBOR (0 : UInt16)).data == #[0]
#guard (toCBOR (255 : UInt16)).data == #[0x18, 255]
#guard (toCBOR (256 : UInt16)).data == #[0x19, 1, 0]
#guard (toCBOR (1000 : UInt16)).data == #[0x19, 3, 0xe8]

#guard (toCBOR (-1000 : Int16)).data == #[0x39, 0x03, 0xe7]
#guard (toCBOR Int16.maxValue).data == #[0x19, 0x7f, 0xff]
#guard (toCBOR Int16.minValue).data == #[0x39, 0x7f, 0xff]

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : UInt16) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Int16) :
    roundtrip x == true := by plausible

/-
# 32-bit integers
-/

instance : ToCBOR UInt32 where
  toCBOR x :=
    if x.toNat < UInt16.size
    then toCBOR x.toUInt16
    else withTag 0x1a (toBEByteArray x)

instance : ToCBOR Int32 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt32
    else adjustTag 0x20 (toCBOR (x.abs.toUInt32 - 1))

instance : FromCBOR UInt32 where
  parse arr :=
    fromFixed arr 0x1a
      (parseMap UInt16 fun x => x.toUInt32)
      fun arr => return (5, <- (arr.take 4).toUInt32BE)

instance : FromCBOR Int32 where
  parse arr := do
    let (signed, sz, x) <- checkSign UInt32 arr
    if signed
    then return (sz, (x+1).toInt32.neg)
    else return (sz, x.toInt32)

-- Test vectors from RFC
#guard (toCBOR (0 : UInt32)).data == #[0]
#guard (toCBOR (255 : UInt32)).data == #[0x18, 255]
#guard (toCBOR (256 : UInt32)).data == #[0x19, 1, 0]
#guard (toCBOR (1000000 : UInt32)).data == #[0x1a, 0, 0x0f, 0x42, 0x40]

#guard (toCBOR (-1000000 : Int32)).data == #[0x3a, 0, 0x0f, 0x42, 0x3f]
#guard (toCBOR Int32.maxValue).data == #[0x1a, 0x7f, 0xff, 0xff, 0xff]
#guard (toCBOR Int32.minValue).data == #[0x3a, 0x7f, 0xff, 0xff, 0xff]

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : UInt32) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Int32) :
    roundtrip x == true := by plausible

/-
# 64-bit integers
-/

instance : ToCBOR UInt64 where
  toCBOR x :=
    if x.toNat < UInt32.size
    then toCBOR x.toUInt32
    else withTag 0x1b (toBEByteArray x)

instance : ToCBOR Int64 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt64
    else adjustTag 0x20 (toCBOR (x.abs.toUInt64 - 1))

instance : FromCBOR UInt64 where
  parse arr :=
    fromFixed arr 0x1b
      (parseMap UInt32 fun x => x.toUInt64)
      fun arr => return (9, <- (arr.take 8).toUInt64BE)

instance : FromCBOR Int64 where
  parse arr := do
    let (signed, sz, x) <- checkSign UInt64 arr
    if signed
    then return (sz, (x+1).toInt64.neg)
    else return (sz, x.toInt64)

-- Test vectors from RFC
#guard (toCBOR (0 : UInt64)).data == #[0]
#guard (toCBOR (255 : UInt64)).data == #[0x18, 255]
#guard (toCBOR (256 : UInt64)).data == #[0x19, 1, 0]
#guard (toCBOR (1000000 : UInt64)).data == #[0x1a, 0, 0x0f, 0x42, 0x40]
#guard (toCBOR (1000000000000 : UInt64)).data ==
                #[0x1b, 0, 0, 0, 0xe8, 0xd4, 0xa5, 0x10, 0]
#guard (toCBOR (18446744073709551615 : UInt64)).data ==
                #[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

#guard (toCBOR (-1000000 : Int64)).data == #[0x3a, 0, 0x0f, 0x42, 0x3f]
#guard (toCBOR Int64.maxValue).data == #[0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
#guard (toCBOR Int64.minValue).data == #[0x3b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

-- TODO: These examples were added after finding a bug in the UInt64 instance
-- The plausible test never caught this bug, so that is interesting.

#guard (roundtrip (0 : UInt64))
#guard (roundtrip (255 : UInt64))
#guard (roundtrip (256 : UInt64))
#guard (roundtrip (1000000 : UInt64))
#guard (roundtrip (1000000000000 : UInt64))
#guard (roundtrip (18446744073709551615 : UInt64))
#guard (roundtrip (-1000000 : Int64))
#guard (roundtrip Int64.maxValue)
#guard (roundtrip Int64.minValue)

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : UInt64) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Int64) :
    roundtrip x == true := by plausible

/-
# Big integers

Note: CBOR does support big integers (major type 0xc2 and 0xc3), however we
don't want to support this on the C-side. These instance silently truncate.
-/

instance : ToCBOR Nat where toCBOR x := toCBOR x.toUInt64
instance : ToCBOR Int where toCBOR x := toCBOR x.toInt64

instance : FromCBOR Nat where parse := parseMap _ UInt64.toNat
instance : FromCBOR Int where parse := parseMap _ Int64.toInt

/-
# Floats

Note, we encode all floats as either 32- or 64-bit IEEE; we do not use 16-bit
formats. This should be OK, it just wastes a few bytes.
-/

instance : ToCBOR Float32 where
  toCBOR f := withTag 0xfa (toBEByteArray f.toBits)

instance : ToCBOR Float where
  toCBOR f := withTag 0xfb (toBEByteArray f.toBits)

instance : FromCBOR Float32 where
  parse arr := do
    if h:arr.size > 0 then
      let b0 := arr[0]
      if b0 == 0xfa then
        let bits <- (arr.sub 1 4).toUInt32BE
        return (5, Float32.ofBits bits)
    throw "expecting float"

instance : FromCBOR Float where
  parse arr := do
    if h:arr.size > 0 then
      let b0 := arr[0]
      if b0 == 0xfa then
        let f32 : Float32 <- fromCBOR arr
        return (5, f32.toFloat)
      if b0 == 0xfb then
        let bits <- (arr.sub 1 8).toUInt64BE
        return (9, Float.ofBits bits)
    throw "expecting float"


-- Test vectors from RFC
def f32_nan : Float32 := 0.0 / 0.0
def f32_inf : Float32 := 1.0 / 0.0
def f32_minf : Float32 := -1.0 / 0.0

#guard (toCBOR (0 : Float32)).data == #[0xfa, 0, 0, 0, 0]
#guard (toCBOR (-0 : Float32)).data == #[0xfa, 0x80, 0, 0, 0]
#guard (toCBOR f32_nan).data == #[0xfa, 0x7f, 0xc0, 0, 0]
#guard (toCBOR f32_inf).data == #[0xfa, 0x7f, 0x80, 0, 0]
#guard (toCBOR f32_minf).data == #[0xfa, 0xff, 0x80, 0, 0]

def f64_nan : Float := 0.0 / 0.0
def f64_inf : Float := 1.0 / 0.0
def f64_minf : Float := -1.0 / 0.0

#guard (toCBOR (0 : Float)).data == #[0xfb, 0,0,0,0, 0,0,0,0]
#guard (toCBOR (-0 : Float)).data == #[0xfb, 0x80, 0,0,0, 0,0,0,0]
#guard (toCBOR f64_nan).data == #[0xfb, 0x7f, 0xf8, 0,0, 0,0,0,0]
#guard (toCBOR f64_inf).data == #[0xfb, 0x7f, 0xf0, 0,0, 0,0,0,0]
#guard (toCBOR f64_minf).data == #[0xfb, 0xff, 0xf0, 0,0, 0,0,0,0]

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Float32) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Float) :
    roundtrip x == true := by plausible

/-
# Strings

Note: there is no support for "terminated strings;" all strings must have a size.
-/

instance : ToCBOR String where
  toCBOR s :=
    let size := toCBOR s.utf8ByteSize.toUInt64
    let size := adjustTag 0x60 size
    size ++ s.toUTF8

instance : FromCBOR String where
  parse arr := do
    let (major, sz, x) <- parseUInt UInt64 arr
    if major != 0x60 then
      throw "expecting string"
    let x := x.toNat
    let arr := (arr.drop sz).take x
    match String.fromUTF8? arr with
    | none => throw "invalid UTF8 string"
    | some s => return (sz + x, s)

-- Test vectors from RFC
#guard (toCBOR "").data == #[0x60]
#guard (toCBOR "a").data == #[0x61, 0x61]
#guard (toCBOR "IETF").data == #[0x64, 0x49, 0x45, 0x54, 0x46]
#guard (toCBOR "· ♥ ·").data == #[0x69, 194, 183, 32, 226, 153, 165, 32, 194, 183]

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : String) :
    roundtrip x == true := by plausible

/-
# Names

Names are just a special case of Strings
-/

instance : ToCBOR Lean.Name where
  toCBOR n := toCBOR n.toString

instance : FromCBOR Lean.Name where
  parse arr := do
    let (sz, s) <- @parse String _ arr
    return (sz, s.toName)

/-
# Pairs

All sequences, are encoded as CBOR "arrays" (major type 4).
-/

instance [ToCBOR a] [ToCBOR b] : ToCBOR (a × b) where
  toCBOR p :=
    let arr1 := toCBOR p.fst
    let arr2 := toCBOR p.snd
    withTag 0x82 (arr1 ++ arr2)

instance [FromCBOR a] [FromCBOR b] : FromCBOR (a × b) where
  parse arr := do
    if h:arr.size > 0 then
      let b0 := arr[0]
      if b0 != 0x82 then
        throw "expecting pair"
      let (sz1, x) <- @parse a _ (arr.drop 1)
      let (sz2, y) <- @parse b _ (arr.drop (1+sz1))
      return (1 + sz1 + sz2, (x, y))
    throw "expecting pair"

-- These tests make sure we are computing the sizes correctly

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : (String × UInt32 × Bool × Bool)) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : (Float × Float32 × Bool)) :
    roundtrip x == true := by plausible

/-
# Lists and Arrays

Lists and arrays are encoded similar to pair above.
-/

instance [ToCBOR a] : ToCBOR (Array a) where
  toCBOR l :=
    let size := toCBOR l.size.toUInt64
    let arrays := l.foldr (fun x arr => toCBOR x ++ arr) (.mk #[])
    adjustTag 0x80 size ++ arrays

instance [FromCBOR a] : FromCBOR (Array a) where
  parse arr := do
    let (major, sz, count) <- parseUInt UInt64 arr
    if major != 0x80 then
      throw "expecting array"
    let mut as := #[]
    let mut size := sz
    let mut b := arr.drop sz
    for _ in [:count.toNat] do
      let (sz, x) <- @parse a _ b
      as := as.push x
      size := size + sz
      b := b.drop sz
    return (size, as)

instance [ToCBOR a] : ToCBOR (List a) where
  toCBOR l := toCBOR l.toArray

instance [FromCBOR a] : FromCBOR (List a) where
  parse := parseMap (Array a) Array.toList

private def one : UInt8 := 1

#guard (toCBOR ([] : List Bool)).data == #[0x80]
#guard (toCBOR [one,2,3]).data == #[0x83,1,2,3]
#guard (toCBOR [[one],[2,3],[4,5]]).data == #[0x83, 0x81,1, 0x82,2,3, 0x82,4,5]

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : List Int32) :
    roundtrip x == true := by plausible

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : List (Bool × List UInt8)) :
    roundtrip x == true := by plausible

/-
# Encoding of arbitrary inductive types

Each inductive type (including structures) have a serde tag assigned to them,
and each constructor also has a tag. We use the CBOR "tagged value" encoding
for this. For each type, we use a 16-bit tag, the first half is the type tag
and the second half is the constructor tag. Following the tag we have a tuple
of the constructor arguments.

The functions below are called by the derived instances to build and parse the
tagged encoding. For simplicity we limit constructors to at most 24 arguments;
this constraint can be lifted by modifying these functions.
TODO: lift this constraint.
-/

def cborTag (typeTag valTag len : Nat) : ByteArray :=
  assert! len < 0x18
  let len := 0x80 ||| len
  .mk #[ 0xd9, typeTag.toUInt8, valTag.toUInt8, len.toUInt8 ]

def parseCBORTag (arr : ByteArray) : Err (Nat × Nat × Nat × ByteArray) := do
  if h:arr.size > 4 then
    if arr[0] != 0xd9 then
      throw "expecting tagged value"
    let typeTag := arr[1]
    let valTag := arr[2]
    let listTag := arr[3] &&& 0xe0
    let listSize := arr[3] &&& 0x1f
    if listTag != 0x80 then
      throw s!"expecting list after tagged value; got {listTag}"
    if listSize >= 0x18 then
      throw s!"expecting small list after tagged value; got {listSize}"
    return (typeTag.toNat, valTag.toNat, listSize.toNat, arr.drop 4)
  throw "expecting tagged value - array too small"

/-
# Options

An option is just an inductive type and we encode it as a tagged value
following the convention above.
-/

instance [ToCBOR a] : ToCBOR (Option a) where
  toCBOR
    | none   => .mk #[ 0xd9, 0xff, 0, 0x80 ]
    | some a => .mk #[ 0xd9, 0xff, 1, 0x81 ] ++ toCBOR a

instance [FromCBOR a] : FromCBOR (Option a) where
  parse arr :=
    match arr.data.take 4 with
    | #[ 0xd9, 0xff, 0, 0x80 ] => return (4, none)
    | #[ 0xd9, 0xff, 1, 0x81 ] => do
      let (sz, v) <- parse (arr.drop 4)
      return (sz + 4, some v)
    | _ => throw "expecting option"

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
  example (x : Option Bool) :
    roundtrip x == true := by plausible
