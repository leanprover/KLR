/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import Extract.C
import KLR.NKI.Basic
import KLR.Python
import KLR.Serde.Attr
import Lean

namespace Extract.Serde
open Lean Meta
open KLR.Serde (Tags)

namespace Ser

-- Return the name of the serialization function for a given simple type
private def serName : SimpleType -> String
  | .bool => "cbor_encode_bool"
  | .nat => "cbor_encode_uint"
  | .int => "cbor_encode_int"
  | .float => "cbor_encode_float"
  | .string => "String_ser"
  | .const n => toString n ++ "_ser"
  | .enum n => toString n ++ "_ser"
  | .option .string => "String_Option_ser"
  | .option (.const n) => s!"{n}_Option_ser"
  | .list .nat => "Nat_List_ser"
  | .list .string => "String_List_ser"
  | .list (.const n)
  | .list (.enum n) => s!"{n}_List_ser"
  | t => panic! s!"unsupport type in serde gen {repr t}"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"bool {serName ty}(FILE *out, {C.genType ty} x){term}"

private def genSig (ty : LeanType) (term : String := ";") : MetaM Unit := do
  let name := ty.name
  let ty := if ty.isEnum then .enum name else .const name
  genSimpleSig ty term

-- TODO: perhaps this should be in Basic.lean (and complete)
private def simpleName : SimpleType -> MetaM Name
  | .const name
  | .enum name => return name
  | .nat => return `Nat
  | .string => return `String
  | ty => throwError "unexpected type {repr ty}."

-- Generate serialization for a structure or inductive constructor.
-- This includes the constructor tag value, followed by an array of
-- the fields (constructor arguments).
private def genFields (tags : Tags) (n : Name) (fs : List Field) : MetaM Unit := do
  let typeTag := tags.fst
  let tags := tags.snd
  let (valTag, var) <-
    match tags.lookup n with
    | some v => pure (v, C.varName n ++ ".")
    | none => match tags.lookup (.str n "mk") with
              | some v => pure (v, "")
              | none => throwError s!"no serde tag for {n} in {tags}"
  IO.println s!"if (!cbor_encode_tag(out, {typeTag}, {valTag}, {fs.length})) return false;"
  for f in fs do
    IO.println s!"if (!{serName f.type}(out, x->{var}{f.name})) return false;"

private def genSer (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .prod name fields => do
      let tags <- KLR.Serde.serdeTags name
      genFields tags name fields
  | .sum name variants => do
      let tags <- KLR.Serde.serdeTags name
      let var := if ty.isEnum then "x" else "x->tag"
      IO.println s!"switch ({var}) \{"
      for v in variants do
        match v with
        | .prod n fs => do
            IO.println s!"case {n}:"
            genFields tags n fs
            IO.println "break;"
        | _ => throwError s!"Expecting product for {name}.{v.name}"
      IO.println "default: return false;"
      IO.println "}"
  IO.println "return true;"
  IO.println "}"

-- Generate serialization for a list type
private def genListSer (ty : SimpleType) : MetaM Unit := do
  genSimpleSig (.list ty) " {"
  let tname := C.genType (.list ty)
  let name <- simpleName ty
  IO.println s!"  u64 count = 0;
  for ({tname} node = x; node; node = node->next) count++;
  if (!cbor_encode_array_start(out, count)) return false;
  for ({tname} node = x; node; node = node->next)
    if (!{serName ty}(out, x->{String.toLower $ C.varName name})) return false;
  return true;
  }"

-- Generate serialization for an option type
private def genOptionSer (ty : SimpleType) : MetaM Unit := do
  genSimpleSig (.option ty) " {"
  IO.println s!"if (!x) \{
      return cbor_encode_option(out, false);
    } else \{
      return cbor_encode_option(out, true) && {serName ty}(out, x);
    }
  }"

private def serHeader : String :=
r#"#include "cbor.h"

static inline bool String_ser(FILE *out, const char *s) {
  return cbor_encode_string(out, s, 0);
}
"#

private def genH (tys : List LeanType) : MetaM Unit := do
  let lists := collectListTypes tys
  let options := collectOptionTypes tys
  tys.forM genSig
  lists.forM (fun ty => genSimpleSig (.list ty))
  options.forM (fun ty => genSimpleSig (.option ty))

private def genC (tys : List LeanType) : MetaM Unit := do
  let lists := collectListTypes tys
  let options := collectOptionTypes tys
  tys.forM genSer
  lists.forM genListSer
  options.forM genOptionSer

def generatePythonH : MetaM Unit := do
  IO.println C.headerH
  IO.println "#include \"ast_python_core.h\"\n"
  genH (<- C.pythonAST)

def generatePythonC : MetaM Unit := do
  IO.println C.headerC
  IO.println serHeader
  IO.println "#include \"ast_python_core.h\""
  IO.println "#include \"serde_python_core.h\""
  genC (<- C.pythonAST)

def generateNkiH : MetaM Unit := do
  IO.println C.headerH
  IO.println "#include \"ast_nki.h\"\n"
  genH (<- C.nkiAST)

def generateNkiC : MetaM Unit := do
  IO.println C.headerC
  IO.println serHeader
  IO.println "#include \"ast_nki.h\""
  IO.println "#include \"serde_nki.h\""
  genC (<- C.nkiAST)

end Ser
