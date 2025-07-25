/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

// This file is automatically generated from KLR.
// Manual edits to this file will be overwritten.

#include "stdc.h"
#include "region.h"
#include "ast_common.h"
#include "ast_nki.h"
#include "topy_nki.h"

#include <Python.h>

PyObject *Bool_topy(bool x) { return x ? Py_True : Py_False; }
PyObject *Nat_topy(u32 x) { return PyLong_FromLong(x); }
PyObject *Int_topy(int x) { return PyLong_FromLong(x); }
PyObject *Float_topy(float x) { return PyFloat_FromDouble(x); }
PyObject *String_topy(const char *x) { return PyUnicode_FromString(x); }

PyObject *construct(const char *name, PyObject *tup) {
  PyObject *mname = PyUnicode_FromString("klr.ast_nki");
  if (!mname)
    return NULL;
  PyObject *m = PyImport_GetModule(mname);
  Py_DECREF(mname);
  if (!m)
    return NULL;
  PyObject *f = PyObject_GetAttrString(m, name);
  Py_DECREF(m);
  if (!f)
    return NULL;
  PyObject *res = PyObject_CallObject(f, tup);
  Py_DECREF(f);
  return res;
}

PyObject *Bool_List_topy(struct Bool_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct Bool_List *node = x; node; node = node->next) {
    PyObject *obj = Bool_topy(node->b);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *Nat_List_topy(struct Nat_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct Nat_List *node = x; node; node = node->next) {
    PyObject *obj = Nat_topy(node->nat);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *Int_List_topy(struct Int_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct Int_List *node = x; node; node = node->next) {
    PyObject *obj = Int_topy(node->i);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *Float_List_topy(struct Float_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct Float_List *node = x; node; node = node->next) {
    PyObject *obj = Float_topy(node->f);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *String_List_topy(struct String_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct String_List *node = x; node; node = node->next) {
    PyObject *obj = String_topy(node->s);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *Bool_Option_topy(bool x) {
  if (!x) {
    return Py_None;
  } else {
    return Bool_topy(x);
  }
}

PyObject *Nat_Option_topy(u32 x) {
  if (!x) {
    return Py_None;
  } else {
    return Nat_topy(x);
  }
}

PyObject *Int_Option_topy(i32 x) {
  if (!x) {
    return Py_None;
  } else {
    return Int_topy(x);
  }
}

PyObject *Float_Option_topy(f32 x) {
  if (!x) {
    return Py_None;
  } else {
    return Float_topy(x);
  }
}

PyObject *String_Option_topy(char *x) {
  if (!x) {
    return Py_None;
  } else {
    return String_topy(x);
  }
}

PyObject *Core_Pos_topy(struct Core_Pos *x) {
  PyObject *tup = PyTuple_New(4);
  if (!tup)
    return NULL;
  {
    PyObject *obj = Nat_topy(x->line);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = Nat_topy(x->column);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = Nat_Option_topy(x->lineEnd);
    if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = Nat_Option_topy(x->columnEnd);
    if (!obj || PyTuple_SetItem(tup, 3, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Pos", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Value_topy(struct NKI_Value *x) {
  switch (x->tag) {
  case NKI_Value_none: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("Value_none", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Value_bool: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = Bool_topy(x->b.value);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Value_bool", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Value_int: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = Int_topy(x->i.value);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Value_int", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Value_float: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = Float_topy(x->f.value);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Value_float", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Value_string: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = String_topy(x->s.value);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Value_string", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Value_tensor: {
    PyObject *tup = PyTuple_New(2);
    if (!tup)
      return NULL;
    {
      PyObject *obj = Nat_List_topy(x->tensor.shape);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = String_topy(x->tensor.dtype);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Value_tensor", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  default:
    return NULL;
  }
}

PyObject *NKI_BinOp_topy(enum NKI_BinOp x) {
  switch (x) {
  case NKI_BinOp_land: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_land", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_lor: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_lor", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_eq: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_eq", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_ne: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_ne", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_lt: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_lt", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_le: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_le", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_gt: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_gt", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_ge: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_ge", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_add: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_add", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_sub: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_sub", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_mul: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_mul", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_div: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_div", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_mod: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_mod", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_pow: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_pow", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_floor: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_floor", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_lshift: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_lshift", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_rshift: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_rshift", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_or: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_or", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_xor: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_xor", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_BinOp_and: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("BinOp_and", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  default:
    return NULL;
  }
}

PyObject *NKI_Expr__topy(struct NKI_Expr_ *x) {
  switch (x->tag) {
  case NKI_Expr_value: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Value_topy(x->value.value);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_value", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Expr_var: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = String_topy(x->var.name);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_var", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Expr_tuple: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_List_topy(x->tuple.elements);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_tuple", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Expr_access: {
    PyObject *tup = PyTuple_New(2);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->access.expr);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Index_List_topy(x->access.indices);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_access", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Expr_binOp: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_BinOp_topy(x->binOp.op);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->binOp.left);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->binOp.right);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_binOp", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Expr_ifExp: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->ifExp.test);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->ifExp.body);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->ifExp.orelse);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_ifExp", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Expr_call: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->call.f);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_List_topy(x->call.args);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Keyword_List_topy(x->call.keywords);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Expr_call", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  default:
    return NULL;
  }
}

PyObject *NKI_Expr_topy(struct NKI_Expr *x) {
  PyObject *tup = PyTuple_New(2);
  if (!tup)
    return NULL;
  {
    PyObject *obj = NKI_Expr__topy(x->expr);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = Core_Pos_topy(x->pos);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Expr", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Index_topy(struct NKI_Index *x) {
  switch (x->tag) {
  case NKI_Index_coord: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->coord.i);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Index_coord", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Index_slice: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_Option_topy(x->slice.l);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_Option_topy(x->slice.u);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_Option_topy(x->slice.step);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Index_slice", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Index_ellipsis: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("Index_ellipsis", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  default:
    return NULL;
  }
}

PyObject *NKI_Keyword_topy(struct NKI_Keyword *x) {
  PyObject *tup = PyTuple_New(2);
  if (!tup)
    return NULL;
  {
    PyObject *obj = String_topy(x->name);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Expr_topy(x->expr);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Keyword", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Pattern_topy(struct NKI_Pattern *x) {
  switch (x->tag) {
  case NKI_Pattern_var: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = String_topy(x->var.name);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Pattern_var", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Pattern_tuple: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Pattern_List_topy(x->tuple.xs);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Pattern_tuple", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  default:
    return NULL;
  }
}

PyObject *NKI_Stmt__topy(struct NKI_Stmt_ *x) {
  switch (x->tag) {
  case NKI_Stmt_expr: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->expr.e);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_expr", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_assert: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->assert.e);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_assert", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_ret: {
    PyObject *tup = PyTuple_New(1);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->ret.e);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_ret", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_declare: {
    PyObject *tup = PyTuple_New(2);
    if (!tup)
      return NULL;
    {
      PyObject *obj = String_topy(x->declare.x);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->declare.ty);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_declare", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_letM: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Pattern_topy(x->letM.p);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_Option_topy(x->letM.ty);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->letM.e);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_letM", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_setM: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->setM.x);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->setM.e);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = Bool_topy(x->setM.accum);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_setM", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_ifStm: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->ifStm.e);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Stmt_List_topy(x->ifStm.thn);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Stmt_List_topy(x->ifStm.els);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_ifStm", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_forLoop: {
    PyObject *tup = PyTuple_New(3);
    if (!tup)
      return NULL;
    {
      PyObject *obj = NKI_Expr_topy(x->forLoop.x);
      if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Expr_topy(x->forLoop.iter);
      if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
        return NULL;
    }
    {
      PyObject *obj = NKI_Stmt_List_topy(x->forLoop.body);
      if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
        return NULL;
    }
    PyObject *res = construct("Stmt_forLoop", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_breakLoop: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("Stmt_breakLoop", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  case NKI_Stmt_continueLoop: {
    PyObject *tup = PyTuple_New(0);
    if (!tup)
      return NULL;
    PyObject *res = construct("Stmt_continueLoop", tup);
    Py_DECREF(tup);
    return res;
    break;
  }
  default:
    return NULL;
  }
}

PyObject *NKI_Stmt_topy(struct NKI_Stmt *x) {
  PyObject *tup = PyTuple_New(2);
  if (!tup)
    return NULL;
  {
    PyObject *obj = NKI_Stmt__topy(x->stmt);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = Core_Pos_topy(x->pos);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Stmt", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Param_topy(struct NKI_Param *x) {
  PyObject *tup = PyTuple_New(2);
  if (!tup)
    return NULL;
  {
    PyObject *obj = String_topy(x->name);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Expr_Option_topy(x->dflt);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Param", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Fun_topy(struct NKI_Fun *x) {
  PyObject *tup = PyTuple_New(5);
  if (!tup)
    return NULL;
  {
    PyObject *obj = String_topy(x->name);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = String_topy(x->file);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = Nat_topy(x->line);
    if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Stmt_List_topy(x->body);
    if (!obj || PyTuple_SetItem(tup, 3, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Param_List_topy(x->args);
    if (!obj || PyTuple_SetItem(tup, 4, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Fun", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Arg_topy(struct NKI_Arg *x) {
  PyObject *tup = PyTuple_New(2);
  if (!tup)
    return NULL;
  {
    PyObject *obj = String_topy(x->name);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Expr_topy(x->value);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Arg", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Kernel_topy(struct NKI_Kernel *x) {
  PyObject *tup = PyTuple_New(4);
  if (!tup)
    return NULL;
  {
    PyObject *obj = String_topy(x->entry);
    if (!obj || PyTuple_SetItem(tup, 0, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Fun_List_topy(x->funs);
    if (!obj || PyTuple_SetItem(tup, 1, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Arg_List_topy(x->args);
    if (!obj || PyTuple_SetItem(tup, 2, obj) == -1)
      return NULL;
  }
  {
    PyObject *obj = NKI_Arg_List_topy(x->globals);
    if (!obj || PyTuple_SetItem(tup, 3, obj) == -1)
      return NULL;
  }
  PyObject *res = construct("Kernel", tup);
  Py_DECREF(tup);
  return res;
}

PyObject *NKI_Expr_List_topy(struct NKI_Expr_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Expr_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Expr_topy(node->expr);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Index_List_topy(struct NKI_Index_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Index_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Index_topy(node->index);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Keyword_List_topy(struct NKI_Keyword_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Keyword_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Keyword_topy(node->keyword);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Expr_Option_topy(struct NKI_Expr *x) {
  if (!x) {
    return Py_None;
  } else {
    return NKI_Expr_topy(x);
  }
}

PyObject *NKI_Pattern_List_topy(struct NKI_Pattern_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Pattern_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Pattern_topy(node->pattern);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Stmt_List_topy(struct NKI_Stmt_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Stmt_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Stmt_topy(node->stmt);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Param_List_topy(struct NKI_Param_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Param_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Param_topy(node->param);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Fun_List_topy(struct NKI_Fun_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Fun_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Fun_topy(node->fun);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}

PyObject *NKI_Arg_List_topy(struct NKI_Arg_List *x) {
  PyObject *list = PyList_New(0);
  if (!list)
    return NULL;
  for (struct NKI_Arg_List *node = x; node; node = node->next) {
    PyObject *obj = NKI_Arg_topy(node->arg);
    if (!obj || PyList_Append(list, obj) == -1)
      return NULL;
    Py_DECREF(obj);
  }
  return list;
}
