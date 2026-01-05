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
import Extract.Cpp
import KLR.NKI.Basic
import KLR.Python
import KLR.Serde.Attr
import Lean

namespace Extract.SerdeCpp
open Lean Meta
open KLR.Serde (Tags)

namespace Ser

-- Return the name of the serialization function for a given simple type
private def serName : SimpleType -> String
  | .const `Lean.Name => "String_ser"
  | .const `KLR.Core.Reg => "Nat_ser"
  | .list (.list t) => s!"List_List_{t.name}_ser"
  | .list t => s!"List_{t.name}_ser"
  | .option (.list (.list t)) => s!"Option_List_List_{t.name}_ser"
  | .option (.list t) => s!"Option_List_{t.name}_ser"
  | .option t => s!"Option_{t.name}_ser"
  | t => s!"{t.name}_ser"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"bool {serName ty}(FILE *out, const {Cpp.genType ty} &value){term}"

private def genSig (ty : LeanType) (term : String := ";") : MetaM Unit := do
  match ty with
  | .simple ty => genSimpleSig ty term
  | .prod n .. => genSimpleSig (.const n) term
  | .sum n .. =>
      let ty := if ty.isEnum then .enum n else .const n
      genSimpleSig ty term

private def genOptionSer (ty : SimpleType) : MetaM Unit := do
  IO.println s!"if (!serialize_option(out, value.has_value))
  return false;

if (value.has_value) \{
  return {serName ty}(out, value.value);
}
return true;"

private def genListSer (ty : SimpleType) : MetaM Unit := do
  IO.println s!"if (!serialize_array_start(out, value.size()))
  return false;

for (const auto &item : value) \{
  if (!{serName ty}(out, item))
    return false;
}
return true;"

-- Generate serialization for a structure or inductive constructor.
-- This includes the constructor tag value, followed by an array of
-- the fields (constructor arguments).
private def genFields (var : String) (fs : List Field) : MetaM Unit := do
  for f in fs do
    IO.println s!"if (!{serName f.type}(out, value{var}->{f.name}))
  return false;"

private def genSer (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .simple (.option (.list ty)) => genOptionSer (.list ty)
  | .simple (.option ty) => genOptionSer ty
  | .simple (.list ty) => genListSer ty
  | .simple _ =>
    IO.println "throw std::runtime_error(\"Serialization not implemented for this simple type\");"
    IO.println "return false;"
  | .prod name fs => do
      match <- KLR.Serde.serdeTags name with
      | (typeTag, [(_, valTag)]) =>
        IO.println s!"if (!serialize_tag(out, {typeTag}, {valTag}, {fs.length}))
  return false;"
        genFields "" fs
        IO.println "return true;"
      | _ => throwError "unexpected tags for product"
  | .sum name variants => do
      let tags <- KLR.Serde.serdeTags name
      if ty.isEnum then
        -- For enums, serialize based on the enum value
        IO.println s!"u8 tag_val = 0;"
        IO.println s!"switch (value) \{"
        for v in variants do
          match v with
          | .prod n _ => do
            match tags.snd.lookup n with
            | some val => do
              IO.println s!"case {Cpp.enumFullName n}: tag_val = {val}; break;"
            | none => throwError s!"no tag for {n}"
          | _ => throwError s!"Expecting product for {name}.{v.name}"
        IO.println "default: return false;"
        IO.println "}"
        IO.println s!"return serialize_tag(out, {tags.fst}, tag_val, 0);"
      else
        IO.println "throw std::runtime_error(\"Serialization not implemented for this sum type\");"
        IO.println "return false;"
  IO.println "}"

end Ser

namespace Des

-- Return the name of the serialization function for a given simple type
private def desName : SimpleType -> String
  | .const `Lean.Name => "String_des"
  | .const `KLR.Core.Reg => "Nat_des"
  | .list (.list t) => s!"List_List_{t.name}_des"
  | .list t => s!"List_{t.name}_des"
  | .option (.list (.list t)) => s!"Option_List_List_{t.name}_des"
  | .option (.list t) => s!"Option_List_{t.name}_des"
  | .option t => s!"Option_{t.name}_des"
  | t => s!"{t.name}_des"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"{Cpp.genType ty} {desName ty}(FILE *in){term}"

private def genSig (ty : LeanType) (term : String := ";") : MetaM Unit := do
  match ty with
  | .simple ty => genSimpleSig ty term
  | .prod n .. => genSimpleSig (.const n) term
  | .sum n .. =>
      let ty := if ty.isEnum then .enum n else .const n
      genSimpleSig ty term

private def genOptionDes (ty : SimpleType) : MetaM Unit := do
  IO.println s!"bool isSome;
if (!deserialize_option(in, &isSome))
  throw std::runtime_error(\"expecting Bool\");

Option<{Cpp.genType ty}> x;
if (isSome)
  x = {desName ty}(in);
return x;"

private def genListDes (ty : SimpleType) : MetaM Unit := do
  let t := Cpp.genType ty
  IO.println s!"u64 size = 0;
if (!deserialize_array_start(in, &size))
  throw std::runtime_error(\"expecting List\");

List<{t}> l;
while (size-- > 0) \{
  {t} b = {desName ty}(in);
  l.push_back(b);
}
return l;"

-- Generate deserialization for a structure or inductive constructor.
-- This includes the constructor tag value, followed by an array of
-- the fields (constructor arguments).
private def genFields (var : String) (fs : List Field) : MetaM Unit := do
  for f in fs do
    IO.println s!"x->{var}{f.name} = {desName f.type}(in);"

private def genDes (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .simple (.option (.list ty)) => genOptionDes (.list ty)
  | .simple (.option ty) => genOptionDes ty
  | .simple (.list ty) => genListDes ty
  | .simple _ => pure ()
  | .prod name fs => do
      match <- KLR.Serde.serdeTags name with
      | (typeTag, [(_, valTag)]) =>
        IO.println s!"u8 t, c, l;
          if (!deserialize_tag(in, &t, &c, &l)) \{
            std::ostringstream msg;
            msg << \"Could not find tag, expecting {name}:{typeTag},{valTag}\";
            throw std::runtime_error(msg.str());
          }
          if (t != {typeTag} || c != {valTag} || l != {fs.length}) \{
            std::ostringstream msg;
            msg << \"Expecting {name}:({typeTag},{valTag},{fs.length})\";
            msg << \" got:(\" << (int)t << \",\" << (int)c << \",\" << (int)l << \")\";
            throw std::runtime_error(msg.str());
          }
          {Cpp.genType (.const name)} x = ptr<{name}>();"
        genFields "" fs
        IO.println "return x;"
      | _ => throwError "unexected tags for product"
  | .sum name variants => do
      let tags <- KLR.Serde.serdeTags name
      IO.println s!"u8 t, c, l;
        if (!deserialize_tag(in, &t, &c, &l)) throw std::runtime_error(\"Could not read tag\");
        if (t != {tags.fst}) throw std::runtime_error(\"Unexpected type tag\");"
      IO.println s!"switch (c) \{"
      for v in variants do
        match v with
        | .prod n fs => do
          match tags.snd.lookup n with
          | some val => do
            IO.println s!"case {val}: \{"
            IO.println s!" if (l != {fs.length}) throw std::runtime_error(\"Wrong number of elements\");"
            if ty.isEnum then
              IO.println s!"return {Cpp.enumFullName n};"
            else
              IO.println s!"Ptr<{Cpp.subclassName n}> x = ptr<{Cpp.subclassName n}>();"
              genFields "" fs
              IO.println "return x;"
            IO.println "break;}"
          | none => throwError s!"no tag for {n}"
        | _ => throwError s!"Expecting product for {name}.{v.name}"
      IO.println "default: throw std::runtime_error(\"Invalid value tag\");"
      IO.println "}"
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

def generateKlrH : MetaM Unit := do
  IO.println <| Cpp.headerH ["klir_ast.hpp"]
  genH (<- commonAST)
  genH (<- klrAST)
  genH (<- fileAST)
  IO.println "}" -- TODO close namepace!

def generateKlrC : MetaM Unit := do
  IO.println <| Cpp.headerC ["klir_serde.hpp"]
  genC (<- commonAST)
  genC (<- klrAST)
  genC (<- fileAST)
  IO.println "}" -- TODO close namepace!
