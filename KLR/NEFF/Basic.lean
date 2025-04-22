/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/

/-
NEFF: Neuron Executable File Format
-/
namespace KLR
namespace NEFF

private def _root_.ByteArray.appendUInt64 (ba : ByteArray) (val : UInt64) : ByteArray :=
  let bytes := ByteArray.mk #[
    val.toUInt8,
    (val >>> 8).toUInt8,
    (val >>> 16).toUInt8,
    (val >>> 24).toUInt8,
    (val >>> 32).toUInt8,
    (val >>> 40).toUInt8,
    (val >>> 48).toUInt8,
    (val >>> 56).toUInt8
  ]
  ba.append bytes

private def _root_.ByteArray.appendUInt32 (ba : ByteArray) (val : UInt32) : ByteArray :=
  let bytes := ByteArray.mk #[
    val.toUInt8,
    (val >>> 8).toUInt8,
    (val >>> 16).toUInt8,
    (val >>> 24).toUInt8
  ]
  ba.append bytes

private def _root_.ByteArray.readUInt64 (arr : ByteArray) (offset : Nat) : UInt64 :=
  if arr.size < offset + 8 then 0 else
  let b0 : UInt64 := arr[offset]!.toUInt64
  let b1 : UInt64 := arr[offset + 1]!.toUInt64
  let b2 : UInt64 := arr[offset + 2]!.toUInt64
  let b3 : UInt64 := arr[offset + 3]!.toUInt64
  let b4 : UInt64 := arr[offset + 4]!.toUInt64
  let b5 : UInt64 := arr[offset + 5]!.toUInt64
  let b6 : UInt64 := arr[offset + 6]!.toUInt64
  let b7 : UInt64 := arr[offset + 7]!.toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

private def _root_.ByteArray.readUInt32 (arr : ByteArray) (offset : Nat) : UInt32 :=
  if arr.size < offset + 4 then 0 else
  let b0 : UInt32 := arr[offset]!.toUInt32
  let b1 : UInt32 := arr[offset + 1]!.toUInt32
  let b2 : UInt32 := arr[offset + 2]!.toUInt32
  let b3 : UInt32 := arr[offset + 3]!.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

local instance : Repr ByteArray where
  reprPrec arr n := reprPrec arr.data n

-- "kelp" was the name of a NEFF ancestor file format
structure Header where
  private mk::
  packaging_version : UInt64 -- 1 - tgz+sha256, 2 - tgz+md5, other - unsupported
  header_size : UInt64 -- 1024 bytes: size of this header, should be the constant 1024?
  data_size : UInt64 -- payload size, no header
  kelp_version_major : UInt64
  kelp_version_minor : UInt64
  kelp_version_build : ByteArray -- 128 bytes
  num_tpb : UInt32 -- Number of chips (cores?) required for efficient execution
  hash : ByteArray -- 64 bytes: SHA256 or MD5 hash of the package (excluding this header)
  uuid : ByteArray -- 32 bytes: Unique ID of this model
  name : ByteArray -- 256 bytes: model name
  requested_tpb_count : UInt32
  tpb_per_node : ByteArray -- 64 bytes: Number of TPBs per Kelp node in the graph, 1 byte per node
  pad : ByteArray -- 632 bytes: padding to make the header 1K in size
  deriving Repr

namespace Header

private def validate (header : Header) : Bool :=
  header.header_size == 1024 &&
  header.kelp_version_build.size == 128 &&
  header.hash.size == 64 &&
  header.uuid.size == 32 &&
  header.name.size == 256 &&
  header.tpb_per_node.size == 64 &&
  header.pad.size == 632

def make
  (packaging_version : UInt64)
  (header_size : UInt64)
  (data_size : UInt64)
  (kelp_version_major : UInt64)
  (kelp_version_minor : UInt64)
  (kelp_version_build : ByteArray)
  (num_tpb : UInt32)
  (hash : ByteArray)
  (uuid : ByteArray)
  (name : ByteArray)
  (requested_tpb_count : UInt32)
  (tpb_per_node : ByteArray)
  (pad : ByteArray) : Option Header :=
  let header := Header.mk
    packaging_version
    header_size
    data_size
    kelp_version_major
    kelp_version_minor
    kelp_version_build
    num_tpb
    hash
    uuid
    name
    requested_tpb_count
    tpb_per_node
    pad
  if !header.validate then none else some header

def serialize (header : Header) : ByteArray := Id.run do
  let mut result := ByteArray.mkEmpty 1024
  result := result.appendUInt64 header.packaging_version
  result := result.appendUInt64 header.header_size
  result := result.appendUInt64 header.data_size
  result := result.appendUInt64 header.kelp_version_major
  result := result.appendUInt64 header.kelp_version_minor
  result := result.append header.kelp_version_build
  result := result.appendUInt32 header.num_tpb
  result := result.append header.hash
  result := result.append header.uuid
  result := result.append header.name
  result := result.appendUInt32 header.requested_tpb_count
  result := result.append header.tpb_per_node
  result := result.append header.pad
  return result

def deserialize (bytes : ByteArray) : Option Header :=
  if bytes.size != 1024 then none else
  let packaging_version := bytes.readUInt64 0
  let header_size := bytes.readUInt64 8
  let data_size := bytes.readUInt64 16
  let kelp_version_major := bytes.readUInt64 24
  let kelp_version_minor := bytes.readUInt64 32
  let kelp_version_build := bytes.extract 40 128
  let num_tpb := bytes.readUInt32 168
  let hash := bytes.extract 172 64
  let uuid := bytes.extract 236 32
  let name := bytes.extract 268 256
  let requested_tpb_count := bytes.readUInt32 524
  let tpb_per_node := bytes.extract 528 64
  let pad := bytes.extract 592 632
  return {
    packaging_version := packaging_version,
    header_size := header_size,
    data_size := data_size,
    kelp_version_major := kelp_version_major,
    kelp_version_minor := kelp_version_minor,
    kelp_version_build := kelp_version_build,
    num_tpb := num_tpb,
    hash := hash,
    uuid := uuid,
    name := name,
    requested_tpb_count := requested_tpb_count,
    tpb_per_node := tpb_per_node,
    pad := pad,
  }

end Header

structure File where
  header : Header
  data : ByteArray
  deriving Repr

namespace File

def validate (neff : File) : Bool :=
  Header.validate neff.header

def serialize (neff : File) : ByteArray := neff.header.serialize.append neff.data

def deserialize (bytes : ByteArray) : Option File := do
  if bytes.size < 1024 then none else
  let headerBytes := bytes.extract 0 1024
  let header <- Header.deserialize headerBytes
  let data := bytes.extract 1024 bytes.size
  if data.size != header.data_size.toNat then none else
  return { header := header, data := data }

def fromHeaderAndData (header : Header) (data : ByteArray) : File :=
  let updatedHeader := { header with data_size := data.size.toUInt64 }
  { header := updatedHeader, data := data }

def read (path : System.FilePath) : IO File := do
  let bytes <- IO.FS.readBinFile path
  match deserialize bytes with
  | none => throw $ IO.userError s!"Can't deserialize {path} as NEFF format"
  | some p => return p

def write (file : File) (path : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile path file.serialize

end File
end NEFF
end KLR
