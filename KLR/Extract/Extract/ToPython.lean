/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Extract.Basic
import Extract.C
import KLR.NKI.Basic
import Lean

namespace Extract.ToPython
open Lean Meta

private def pyName : Name -> String
  | .str _ s => s
  | _ => panic! "bad python name"

private def pyName2 (n1 n2 : Name) : String :=
  under (pyName n1) ++ (pyName n2).toLower
where
  under | "" => ""
        | s => if s.endsWith "_" then s else s ++ "_"

-- Return the name of the conversion function for a given simple type
private def fnName : SimpleType -> String
  | t => s!"{t.name}_topy"

private def genSimpleSig (ty : SimpleType) (term : String := ";") : MetaM Unit := do
  if term != ";" then
    IO.println ""
  IO.println s!"PyObject* {fnName ty}({C.genType ty} x){term}"

private def genSig (ty : LeanType) (term : String := ";") : MetaM Unit := do
  match ty with
  | .simple ty => genSimpleSig ty term
  | .prod n .. => genSimpleSig (.const n) term
  | .sum n .. =>
      let ty := if ty.isEnum then .enum n else .const n
      genSimpleSig ty term

-- Generate conversion for a structure or inductive constructor.
private def genFields (name var : String) (fs : List Field) : MetaM Unit := do
  IO.println s!"PyObject *tup = PyTuple_New({fs.length});"
  IO.println "if (!tup) return NULL;"
  let mut n := 0
  for f in fs do
    IO.println "{"
    IO.println s!"PyObject *obj = {fnName f.type}(x->{var}{f.name});"
    IO.println s!"if (!obj || PyTuple_SetItem(tup, {n}, obj) == -1) return NULL;"
    IO.println "}"
    n := n + 1
  IO.println s!"PyObject *res = construct(\"{name}\", tup);"
  IO.println "Py_DECREF(tup);"
  IO.println "return res;"

-- Generate serialization for a list type
private def genListSer (ty : SimpleType) : MetaM Unit := do
  let tname := C.genType (.list ty)
  let vname := (C.varName ty.name).toLower
  IO.println s!"PyObject *list = PyList_New(0);
  if (!list) return NULL;
  for ({tname} node = x; node; node = node->next) \{
    PyObject *obj = {fnName ty}(x->{vname});
    if (!obj || PyList_Append(list, obj) == -1) return NULL;
    Py_DECREF(obj);
  }
  return list;"

-- Generate serialization for an option type
private def genOptionSer (ty : SimpleType) : MetaM Unit := do
  IO.println s!"if (!x) \{
      return Py_None;
    } else \{
      return {fnName ty}(x);
    }"

private def genSer (ty : LeanType) : MetaM Unit := do
  genSig ty " {"
  match ty with
  | .simple (.option ty) => genOptionSer ty
  | .simple (.list ty) => genListSer ty
  | .simple _ => pure ()
  | .prod name fs => do
      genFields (pyName name) "" fs
  | .sum name variants => do
      let var := if ty.isEnum then "x" else "x->tag"
      IO.println s!"switch ({var}) \{"
      for v in variants do
        match v with
        | .prod n fs => do
            IO.println s!"case {n}: \{"
            genFields (pyName2 name n) (C.varName n ++ ".") fs
            IO.println "break;"
            IO.println "}"
        | _ => throwError s!"Expecting product for {name}.{v.name}"
      IO.println "default: return NULL;"
      IO.println "}"
  IO.println "}"

private def basic : String := "
PyObject* Bool_topy(bool x) { return x ? Py_True : Py_False; }
PyObject* Nat_topy(u32 x) { return PyLong_FromLong(x); }
PyObject* Int_topy(int x) { return PyLong_FromLong(x); }
PyObject* Float_topy(float x) { return PyFloat_FromDouble(x); }
PyObject* String_topy(const char *x) { return PyUnicode_FromString(x); }

PyObject* construct(const char *name, PyObject *tup) {
  PyObject *mname = PyUnicode_FromString(\"klr.ast_nki\");
  if (!mname) return NULL;
  PyObject *m = PyImport_GetModule(mname);
  Py_DECREF(mname);
  if (!m) return NULL;
  PyObject *f = PyObject_GetAttrString(m, name);
  Py_DECREF(m);
  if (!f) return NULL;
  PyObject *res = PyObject_CallObject(f, tup);
  Py_DECREF(f);
  return res;
}"

def generateNkiH : MetaM Unit := do
  IO.println <| C.headerC [ "ast_common.h", "ast_nki.h" ]
  IO.println "#include <Python.h>"
  (<- C.nkiAST).forM genSig

def generateNkiC : MetaM Unit := do
  IO.println <| C.headerC [ "ast_common.h", "ast_nki.h", "topy_nki.h" ]
  IO.println "#include <Python.h>"
  IO.println basic
  (<- C.commonAST).forM genSer
  (<- C.nkiAST).forM genSer
