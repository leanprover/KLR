/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import Extract.C
import Extract.Cpp
import KLR.NKI.Basic
import KLR.Python
import KLR.Serde.Attr
import Lean

namespace Extract.SerdeCpp
open Lean Meta
open KLR.Serde (Tags)

namespace Des

-- Return the name of the serialization function for a given simple type
private def desName : SimpleType -> String
  | .const `Lean.Name => "String_des"
  | .const `KLR.Core.Reg => "Nat_des"
  | t => s!"{t.name}_des"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"bool {desName ty}(FILE *in, {Cpp.genType ty}& x){term}"

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
    IO.println s!"if (!{desName f.type}(in, &(*x)->{var}{f.name}))
      return false;"

private def genDes (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .simple (.option ty) -- => genOptionDes ty
  | .simple (.list ty) -- => genListDes ty
  | .simple _ => pure ()
  | .prod name fs => do
      match <- KLR.Serde.serdeTags name with
      | (typeTag, [(_, valTag)]) =>
        IO.println s!"u8 t, c, l;
          if (!deserialize_tag(in, &t, &c, &l)) return false;
          if (t != {typeTag} || c != {valTag} || l != {fs.length})
            return false;
          *x = static_cast<{name}*>(region_alloc(region, sizeof(**x)));"
        genFields "" fs
      | _ => throwError "unexected tags for product"
  | .sum name variants => do
      let tags <- KLR.Serde.serdeTags name
      IO.println s!"u8 t, c, l;
        if (!deserialize_tag(in, &t, &c, &l)) return false;
        if (t != {tags.fst}) return false;"
      if ty.isEnum then
        IO.println "(void)region;"
      else
        IO.println s!"*x = static_cast<{name}*>(region_alloc(region, sizeof(**x)));"
      IO.println s!"switch (c) \{"
      for v in variants do
        match v with
        | .prod n fs => do
          match tags.snd.lookup n with
          | some val => do
            IO.println s!"case {val}:"
            IO.println s!" if (l != {fs.length}) return false;"
            if ty.isEnum
            then IO.println s!"*x = {Cpp.enumFullName n};"
            else
              genFields (Cpp.varName n ++ ".") fs
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
  --tys.forM Ser.genSig
  --IO.println ""
  tys.forM Des.genSig

private def genC (tys : List LeanType) : MetaM Unit := do
  --tys.forM Ser.genSer
  --IO.println ""
  tys.forM Des.genDes

def generateKlrH : MetaM Unit := do
  IO.println <| Cpp.headerH ["klir_ast.hpp"]
  genH (<- C.klrAST)

def generateKlrC : MetaM Unit := do
  IO.println <| Cpp.headerC ["klir_serde.hpp"]
  genC (<- C.commonAST)
  genC (<- C.klrAST)
  genC (<- C.fileAST)
