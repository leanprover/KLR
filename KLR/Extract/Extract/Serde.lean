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
  | .const `Lean.Name => "String_ser"
  | .const `KLR.Core.Reg => "cbor_encode_uint"
  | t => s!"{t.name}_ser"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"bool {serName ty}(FILE *out, {C.genType ty} x){term}"

private def genSig (ty : LeanType) (term : String := ";") : MetaM Unit := do
  match ty with
  | .simple ty => genSimpleSig ty term
  | .prod n .. => genSimpleSig (.const n) term
  | .sum n .. =>
      let ty := if ty.isEnum then .enum n else .const n
      genSimpleSig ty term

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

-- Generate serialization for a list type
private def genListSer (ty : SimpleType) : MetaM Unit := do
  let tname := C.genType (.list ty)
  let vname := (C.varName ty.name).toLower
  IO.println s!"  u64 count = 0;
  for ({tname} node = x; node; node = node->next) count++;
  if (!cbor_encode_array_start(out, count)) return false;
  for ({tname} node = x; node; node = node->next)
    if (!{serName ty}(out, node->{vname})) return false;"

-- Generate serialization for an option type
private def genOptionSer (ty : SimpleType) : MetaM Unit := do
  IO.println s!"if (!x) \{
      return cbor_encode_option(out, false);
    } else \{
      return cbor_encode_option(out, true) && {serName ty}(out, x);
    }"

private def genSer (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .simple (.option ty) => genOptionSer ty
  | .simple (.list ty) => genListSer ty
  | .simple _ => pure ()
  | .prod name fs => do
      let tags <- KLR.Serde.serdeTags name
      genFields tags name fs
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

end Ser

namespace Des

-- Return the name of the serialization function for a given simple type
private def desName : SimpleType -> String
  | .const `Lean.Name => "String_des"
  | .const `KLR.Core.Reg => "Nat_des"
  | t => s!"{t.name}_des"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"bool {desName ty}(FILE *in, struct region *region, {C.genType ty}* x){term}"

private def genSig (ty : LeanType) (term : String := ";") : MetaM Unit := do
  match ty with
  | .simple ty => genSimpleSig ty term
  | .prod n .. => genSimpleSig (.const n) term
  | .sum n .. =>
      let ty := if ty.isEnum then .enum n else .const n
      genSimpleSig ty term

-- Generate deserialization for a structure or inductive constructor.
-- This includes the constructor tag value, followed by an array of
-- the fields (constructor arguments).
private def genFields (var : String) (fs : List Field) : MetaM Unit := do
  for f in fs do
    IO.println s!"if (!{desName f.type}(in, region, &(*x)->{var}{f.name}))
      return false;"

-- Generate deserialization for a list type
private def genListDes (ty : SimpleType) : MetaM Unit := do
  let tname := C.genType (.list ty)
  let vname := (C.varName ty.name).toLower
  IO.println s!"u64 count = 0;
    if (!cbor_decode_array_start(in, &count)) return false;
    {tname} current = *x = NULL;
    for (; count > 0; count--) \{
      {tname} node = region_alloc(region, sizeof(*node));
      node->next = NULL;
      if (!current) \{
        *x = current = node;
      } else \{
        current->next = node;
        current = node;
      }
      if (!{desName ty}(in, region, &node->{vname})) return false;
    }"

-- Generate serialization for an option type
private def genOptionDes (ty : SimpleType) : MetaM Unit := do
  IO.println s!"bool isSome;
    if (!cbor_decode_option(in, &isSome)) return false;
    if (!isSome) *x = 0;
    else return {desName ty}(in, region, x);"

private def genDes (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .simple (.option ty) => genOptionDes ty
  | .simple (.list ty) => genListDes ty
  | .simple _ => pure ()
  | .prod name fs => do
      match <- KLR.Serde.serdeTags name with
      | (typeTag, [(_, valTag)]) =>
        IO.println s!"u8 t, c, l;
          if (!cbor_decode_tag(in, &t, &c, &l)) return false;
          if (t != {typeTag} || c != {valTag} || l != {fs.length})
            return false;
          *x = region_alloc(region, sizeof(**x));"
        genFields "" fs
      | _ => throwError "unexected tags for product"
  | .sum name variants => do
      let tags <- KLR.Serde.serdeTags name
      IO.println s!"u8 t, c, l;
        if (!cbor_decode_tag(in, &t, &c, &l)) return false;
        if (t != {tags.fst}) return false;"
      if ty.isEnum then
        IO.println "(void)region;"
      else
        IO.println "*x = region_alloc(region, sizeof(**x));"
      IO.println s!"switch (c) \{"
      for v in variants do
        match v with
        | .prod n fs => do
          match tags.snd.lookup n with
          | some val => do
            IO.println s!"case {val}:"
            IO.println s!" if (l != {fs.length}) return false;"
            if ty.isEnum
            then IO.println s!"*x = {n};"
            else
              genFields (C.varName n ++ ".") fs
              IO.println s!"(*x)->tag = {n};"
            IO.println "break;"
          | none => throwError s!"no tag for {n}"
        | _ => throwError s!"Expecting product for {name}.{v.name}"
      IO.println "default: return false;"
      IO.println "}"
  IO.println "return true;"
  IO.println "}"

end Des

private def genH (tys : List LeanType) : MetaM Unit := do
  tys.forM Ser.genSig
  IO.println ""
  tys.forM Des.genSig

private def genC (tys : List LeanType) : MetaM Unit := do
  tys.forM Ser.genSer
  IO.println ""
  tys.forM Des.genDes

def generateCommonH : MetaM Unit := do
  IO.println <| C.headerH ["ast_common.h"]
  genH (<- C.commonAST)

def generateCommonC : MetaM Unit := do
  IO.println <| C.headerC ["cbor.h", "serde_common.h"]
  genC (<- C.commonAST)

def generateFileH : MetaM Unit := do
  IO.println <| C.headerC [ "cbor.h", "ast_file.h", "serde_common.h"]
  genH (<- C.fileAST)

def generateFileC : MetaM Unit := do
  IO.println <| C.headerC ["serde_file.h", "serde_python_core.h", "serde_nki.h"]
  genC (<- C.fileAST)

def generatePythonH : MetaM Unit := do
  IO.println <| C.headerH ["ast_common.h", "ast_python_core.h"]
  genH (<- C.pythonAST)

def generatePythonC : MetaM Unit := do
  IO.println <| C.headerC ["cbor.h", "serde_common.h", "serde_python_core.h"]
  genC (<- C.pythonAST)

def generateNkiH : MetaM Unit := do
  IO.println <| C.headerH ["ast_common.h", "ast_nki.h"]
  genH (<- C.nkiAST)

def generateNkiC : MetaM Unit := do
  IO.println <| C.headerC ["cbor.h", "serde_common.h", "serde_nki.h"]
  genC (<- C.nkiAST)

def generateKlrH : MetaM Unit := do
  IO.println <| C.headerH ["ast_common.h", "ast_klir.h"]
  genH (<- C.klrAST)

def generateKlrC : MetaM Unit := do
  IO.println <| C.headerC ["cbor.h", "serde_common.h", "serde_klir.h"]
  genC (<- C.klrAST)
