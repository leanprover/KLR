/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.NKI.Basic
import KLR.Python
import KLR.Serde
import KLR.Util

/-
# KLR File format(s)

This file describes a uniform format for all of the KLR artifacts.

The motivation for this code is: when we are interacting with the production
compiler, we want to have one "KLIR Binary" file format. This format is just a
CBOR encoded Lean type, but we sometimes want a KLIR value, and sometimes we
want a NKI AST, and sometimes we want a Python AST, etc. In addition, we want
to allow for non-binary versions, like JSON or S-Expr, for development and
debugging purposes.

To this end, this file contains two things:

1. A simple inductive type that defines all of the things that can appear in a
KLR file. We simply encode this "top level" inductive type to indicate which of
the things we have.

2. Utility functions to read and write the various formats. The read function
can automatically detect which kind of file we have.
-/

namespace KLR.File
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR parseCBOR fromCBOR toCBOR)
open Util (FromSexp ToSexp toSexp)

-- Note: this serde tag can be anything we want, but I am choosing
-- something that external tools will not recognize, just in case.

@[serde tag = 0xec]
inductive Contents where
  | python (kernel : Python.Kernel)
  | nki (kernel : KLR.NKI.Kernel)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

inductive Format where
  | any | cbor | json | sexp
  deriving BEq, Repr

private def readCBOR (arr : ByteArray) : Err Contents := do
  let (arr, _) <- @parseCBOR Serde.KLRFile _ arr
  let (arr, _) <- @parseCBOR Serde.KLRMetaData _ arr
  fromCBOR arr

private def writeCBOR (c : Contents) : ByteArray :=
  let header := toCBOR { : KLR.Serde.KLRFile }
  let mdata := toCBOR { : KLR.Serde.KLRMetaData }
  header ++ mdata ++ toCBOR c

private def arrayToString (arr : ByteArray) : Err String := do
  match String.fromUTF8? arr with
  | some s => return s
  | none => throw "Not a valid UTF8 String"

private def parse (arr : ByteArray) (format : Format) : Err Contents := do
  match format with
  | .any => throw "parse: invalid arguments"
  | .cbor => readCBOR arr
  | .json => Lean.fromJson? (<- Lean.Json.parse (<- arrayToString arr))
  | .sexp => throw "not implemented"

def parseBytes (arr : ByteArray) (format : Format) : Err Contents :=
  match format with
  | .any => do
    -- Try in order of most to least likely
    for f in [ .cbor, .sexp, .json ] do
      try let c <- parse arr f; return c
      catch _ => continue
    throw "unrecognized format"
  | _ => parse arr format

-- Convenient APIs

class FromContents (a : Type) where
  fromContents : Contents -> Err a

instance : FromContents Python.Kernel where
  fromContents | .python k => return k
               | _ => throw "expecting Python Kernel"

instance : FromContents NKI.Kernel where
  fromContents | .nki k => return k
               | _ => throw "expecting NKI Kernel"

instance : Coe Python.Kernel Contents := ⟨ .python ⟩
instance : Coe NKI.Kernel Contents := ⟨ .nki ⟩

/--
Read the bytes in `arr` as `format` and return a Lean value. The format can be
CBOR, Json, or Sexp. The special format "any" can be used to have the function
try all of the formats and return the first one that is successful.
-/
def readKLRBytes [FromContents a] (arr : ByteArray) (format : Format := .any) : Err a := do
  FromContents.fromContents (<- parseBytes arr format)

/--
Read the `file` as `format` and return a Lean value. The format can be CBOR,
Json, or Sexp. The special format "any" can be used to have the function try
all of the formats and return the first one that is successful.
-/
def readKLRFile [FromContents a] (file : System.FilePath) (format : Format := .any) : IO a := do
  readKLRBytes (<- IO.FS.readBinFile file) format

/--
Write a KLR file using the specified format. If `any` is used, the default is CBOR.
-/
def writeKLRFile [Coe a Contents] (file : System.FilePath) (format : Format := .any) (x : a) : IO Unit := do
  let contents : Contents := Coe.coe x
  match format with
  | .any
  | .cbor => IO.FS.writeBinFile file (writeCBOR contents)
  | .json => IO.FS.writeFile file <| toString <| Lean.toJson contents
  | .sexp => IO.FS.writeFile file <| toString <| toSexp contents
