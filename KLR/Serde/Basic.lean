/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Util

/-
# Encoding and Decoding of Basic CBOR values

https://cbor.io
https://www.rfc-editor.org/rfc/rfc8949.html
-/

namespace KLR.Serde

class ToCBOR (a : Type u) where
  toCBOR : a -> ByteArray

export ToCBOR (toCBOR)

class FromCBOR (a : Type u) where
  parseCBOR' (arr : ByteArray) : Err (Nat × a)

export FromCBOR (parseCBOR')

def parseCBOR [FromCBOR a] (arr : ByteArray) : Err (ByteArray × a) :=
  (parseCBOR' arr).map fun (sz, x) =>
    (.mk (arr.data.drop sz), x)

def fromCBOR [FromCBOR a] (arr : ByteArray) : Err a :=
  (parseCBOR' arr).map Prod.snd

/-
# Booleans
-/

instance : ToCBOR Bool where
  toCBOR
    | false => .mk #[0xf4]
    | true  => .mk #[0xf5]

instance : FromCBOR Bool where
  parseCBOR' arr := do
    if h:arr.size > 0 then
      match arr[0]'h with
      | 0xf4 => return (1, false)
      | 0xf5 => return (1, true)
      | _ => throw "expecting boolean"
    else throw "expecting Boolean"

-- Only two cases, so no plausible for this test
#eval do
  match fromCBOR (toCBOR true) with
  | .ok true => pure ()
  | _ => throwError "CBOR Bool mismatch: true"
  match fromCBOR (toCBOR false) with
  | .ok false => pure ()
  | _ => throwError "CBOR Bool mismatch: false"

/-
# Integers
-/

instance : ToCBOR UInt8 where
  toCBOR x :=
    if x <= 23 then .mk #[x]
    else .mk #[ 0x18, x ]

#guard (toCBOR (0 : UInt8)).data == #[0]
#guard (toCBOR (23 : UInt8)).data == #[23]
#guard (toCBOR (24 : UInt8)).data == #[0x18, 24]
#guard (toCBOR (100 : UInt8)).data == #[0x18, 0x64]
#guard (toCBOR (255 : UInt8)).data == #[0x18, 255]

instance : ToCBOR UInt16 where
  toCBOR x :=
    if x.toNat < UInt8.size then
      toCBOR x.toUInt8
    else
      .mk #[ 0x19, (x >>> 8).toUInt8, x.toUInt8 ]

#guard (toCBOR (0 : UInt16)).data == #[0]
#guard (toCBOR (255 : UInt16)).data == #[0x18, 255]
#guard (toCBOR (256 : UInt16)).data == #[0x19, 1, 0]
#guard (toCBOR (1000 : UInt16)).data == #[0x19, 3, 0xe8]

instance : ToCBOR UInt32 where
  toCBOR x :=
    if x.toNat < UInt16.size then
      toCBOR x.toUInt16
    else
      .mk #[0x1a, (x >>> 24).toUInt8,
                  (x >>> 16).toUInt8,
                  (x >>>  8).toUInt8,
                  (x >>>  0).toUInt8 ]

#guard (toCBOR (0 : UInt32)).data == #[0]
#guard (toCBOR (255 : UInt32)).data == #[0x18, 255]
#guard (toCBOR (256 : UInt32)).data == #[0x19, 1, 0]
#guard (toCBOR (1000000 : UInt32)).data == #[0x1a, 0, 0x0f, 0x42, 0x40]

instance : ToCBOR UInt64 where
  toCBOR x :=
    if x.toNat < UInt32.size then
      toCBOR x.toUInt32
    else
      .mk #[0x1b, (x >>> 56).toUInt8,
                  (x >>> 48).toUInt8,
                  (x >>> 40).toUInt8,
                  (x >>> 32).toUInt8,
                  (x >>> 24).toUInt8,
                  (x >>> 16).toUInt8,
                  (x >>>  8).toUInt8,
                  (x >>>  0).toUInt8 ]

#guard (toCBOR (0 : UInt64)).data == #[0]
#guard (toCBOR (255 : UInt64)).data == #[0x18, 255]
#guard (toCBOR (256 : UInt64)).data == #[0x19, 1, 0]
#guard (toCBOR (1000000 : UInt64)).data == #[0x1a, 0, 0x0f, 0x42, 0x40]
#guard (toCBOR (1000000000000 : UInt64)).data ==
                #[0x1b, 0, 0, 0, 0xe8, 0xd4, 0xa5, 0x10, 0]
#guard (toCBOR (18446744073709551615 : UInt64)).data ==
                #[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]


-- Convert a Nat to a big-endian byte array
private def bytesOfNat (n : Nat) : Array UInt8 :=
  let rec loop n :=
    if n == 0 then #[]
    else (loop (n >>> 8)).push n.toUInt8
   termination_by n
   decreasing_by induction n; trivial; omega
  loop n

instance : ToCBOR Nat where
  toCBOR x :=
    if x < UInt64.size then
      toCBOR x.toUInt64
    else
      let bytes := bytesOfNat x
      let tag := (toCBOR bytes.size.toUInt64).data
      let tag := tag.set! 0 (tag[0]! ||| 0x40)
      .mk (#[0xc2] ++ tag ++ bytes)

#guard (toCBOR (0 : Nat)).data == #[0]
#guard (toCBOR (1000000000000 : Nat)).data ==
                #[0x1b, 0, 0, 0, 0xe8, 0xd4, 0xa5, 0x10, 0]
#guard (toCBOR (18446744073709551615 : Nat)).data ==
                #[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
#guard (toCBOR (18446744073709551616 : Nat)).data ==
                #[0xc2, 0x49, 1, 0, 0, 0, 0, 0, 0, 0, 0]

-- negative integers a similar to positive ones with an extra bit set
private def adjustTag (bit : UInt8) (a : ByteArray) : ByteArray :=
  .mk $ a.data.set! 0 (a.data[0]! ||| bit)

instance : ToCBOR Int8 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt8
    else adjustTag 0x20 (toCBOR (x.abs.toUInt8 - 1))

#guard (toCBOR (-1 : Int8)).data == #[0x20]
#guard (toCBOR (-10 : Int8)).data == #[0x29]
#guard (toCBOR (-100 : Int8)).data == #[0x38, 0x63]
#guard (toCBOR Int8.maxValue).data == #[0x18, 0x7f]
#guard (toCBOR Int8.minValue).data == #[0x38, 0x7f]

instance : ToCBOR Int16 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt16
    else adjustTag 0x20 (toCBOR (x.abs.toUInt16 - 1))

#guard (toCBOR (-1000 : Int16)).data == #[0x39, 0x03, 0xe7]
#guard (toCBOR Int16.maxValue).data == #[0x19, 0x7f, 0xff]
#guard (toCBOR Int16.minValue).data == #[0x39, 0x7f, 0xff]

instance : ToCBOR Int32 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt32
    else adjustTag 0x20 (toCBOR (x.abs.toUInt32 - 1))

#guard (toCBOR (-1000000 : Int32)).data == #[0x3a, 0, 0x0f, 0x42, 0x3f]
#guard (toCBOR Int32.maxValue).data == #[0x1a, 0x7f, 0xff, 0xff, 0xff]
#guard (toCBOR Int32.minValue).data == #[0x3a, 0x7f, 0xff, 0xff, 0xff]

instance : ToCBOR Int64 where
  toCBOR x :=
    if x >= 0 then toCBOR x.toUInt64
    else adjustTag 0x20 (toCBOR (x.abs.toUInt64 - 1))

#guard (toCBOR (-1000000 : Int64)).data == #[0x3a, 0, 0x0f, 0x42, 0x3f]
#guard (toCBOR Int64.maxValue).data == #[0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
#guard (toCBOR Int64.minValue).data == #[0x3b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

instance : ToCBOR Int where
  toCBOR
    | .ofNat n => toCBOR n
    | .negSucc n =>
        let tag := if n < UInt64.size then 0x20 else 0x01
        adjustTag tag (toCBOR n)

#guard (toCBOR (-1000000 : Int)).data == #[0x3a, 0, 0x0f, 0x42, 0x3f]
#guard (toCBOR (-0x1_00000000_00000000 : Int)).data == #[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
#guard (toCBOR (-0x1_00000000_00000001 : Int)).data == #[0xc3, 0x49, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-
# Strings, Lists, Arrays
-/

instance : ToCBOR ByteArray where
  toCBOR arr :=
    let size := toCBOR arr.size
    let size := adjustTag 0x40 size
    size ++ arr

#guard (toCBOR $ ByteArray.mk #[]).data == #[0x40]
#guard (toCBOR $ ByteArray.mk #[1,2,3,4]).data == #[0x44,1,2,3,4]

instance : ToCBOR String where
  toCBOR s :=
    let size := toCBOR s.utf8ByteSize.toUInt64
    let size := adjustTag 0x60 size
    size ++ s.toUTF8

#guard (toCBOR "").data == #[0x60]
#guard (toCBOR "a").data == #[0x61, 0x61]
#guard (toCBOR "IETF").data == #[0x64, 0x49, 0x45, 0x54, 0x46]
#guard (toCBOR "· ♥ ·").data == #[0x69, 194, 183, 32, 226, 153, 165, 32, 194, 183]

instance [ToCBOR a] : ToCBOR (List a) where
  toCBOR l :=
    let size := toCBOR l.length.toUInt64
    let size := adjustTag 0x80 size
    let arrays := l.foldr (fun x arr => toCBOR x ++ arr) (.mk #[])
    size ++ arrays

#guard (toCBOR ([] : List Nat)).data == #[0x80]
#guard (toCBOR [1,2,3]).data == #[0x83,1,2,3]
#guard (toCBOR [[1],[2,3],[4,5]]).data == #[0x83, 0x81,1, 0x82,2,3, 0x82,4,5]
