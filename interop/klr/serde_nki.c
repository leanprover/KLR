/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

// This file is automatically generated from KLR.
// Manual edits to this file will be overwritten.

#include "stdc.h"
#include "region.h"
#include "cbor.h"
#include "serde_common.h"
#include "serde_nki.h"

bool NKI_Value_ser(FILE *out, struct NKI_Value *x) {
  switch (x->tag) {
  case NKI_Value_none:
    if (!cbor_encode_tag(out, 1, 0, 0))
      return false;
    break;
  case NKI_Value_bool:
    if (!cbor_encode_tag(out, 1, 1, 1))
      return false;
    if (!cbor_encode_bool(out, x->b.value))
      return false;
    break;
  case NKI_Value_int:
    if (!cbor_encode_tag(out, 1, 2, 1))
      return false;
    if (!cbor_encode_int(out, x->i.value))
      return false;
    break;
  case NKI_Value_float:
    if (!cbor_encode_tag(out, 1, 3, 1))
      return false;
    if (!cbor_encode_float(out, x->f.value))
      return false;
    break;
  case NKI_Value_string:
    if (!cbor_encode_tag(out, 1, 4, 1))
      return false;
    if (!String_ser(out, x->s.value))
      return false;
    break;
  case NKI_Value_tensor:
    if (!cbor_encode_tag(out, 1, 5, 2))
      return false;
    if (!Nat_List_ser(out, x->tensor.shape))
      return false;
    if (!String_ser(out, x->tensor.dtype))
      return false;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_BinOp_ser(FILE *out, enum NKI_BinOp x) {
  switch (x) {
  case NKI_BinOp_land:
    if (!cbor_encode_tag(out, 2, 0, 0))
      return false;
    break;
  case NKI_BinOp_lor:
    if (!cbor_encode_tag(out, 2, 1, 0))
      return false;
    break;
  case NKI_BinOp_eq:
    if (!cbor_encode_tag(out, 2, 2, 0))
      return false;
    break;
  case NKI_BinOp_ne:
    if (!cbor_encode_tag(out, 2, 3, 0))
      return false;
    break;
  case NKI_BinOp_lt:
    if (!cbor_encode_tag(out, 2, 4, 0))
      return false;
    break;
  case NKI_BinOp_le:
    if (!cbor_encode_tag(out, 2, 5, 0))
      return false;
    break;
  case NKI_BinOp_gt:
    if (!cbor_encode_tag(out, 2, 6, 0))
      return false;
    break;
  case NKI_BinOp_ge:
    if (!cbor_encode_tag(out, 2, 7, 0))
      return false;
    break;
  case NKI_BinOp_add:
    if (!cbor_encode_tag(out, 2, 8, 0))
      return false;
    break;
  case NKI_BinOp_sub:
    if (!cbor_encode_tag(out, 2, 9, 0))
      return false;
    break;
  case NKI_BinOp_mul:
    if (!cbor_encode_tag(out, 2, 10, 0))
      return false;
    break;
  case NKI_BinOp_div:
    if (!cbor_encode_tag(out, 2, 11, 0))
      return false;
    break;
  case NKI_BinOp_mod:
    if (!cbor_encode_tag(out, 2, 12, 0))
      return false;
    break;
  case NKI_BinOp_pow:
    if (!cbor_encode_tag(out, 2, 13, 0))
      return false;
    break;
  case NKI_BinOp_floor:
    if (!cbor_encode_tag(out, 2, 14, 0))
      return false;
    break;
  case NKI_BinOp_lshift:
    if (!cbor_encode_tag(out, 2, 15, 0))
      return false;
    break;
  case NKI_BinOp_rshift:
    if (!cbor_encode_tag(out, 2, 16, 0))
      return false;
    break;
  case NKI_BinOp_or:
    if (!cbor_encode_tag(out, 2, 17, 0))
      return false;
    break;
  case NKI_BinOp_xor:
    if (!cbor_encode_tag(out, 2, 18, 0))
      return false;
    break;
  case NKI_BinOp_and:
    if (!cbor_encode_tag(out, 2, 19, 0))
      return false;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Expr__ser(FILE *out, struct NKI_Expr_ *x) {
  switch (x->tag) {
  case NKI_Expr_value:
    if (!cbor_encode_tag(out, 4, 0, 1))
      return false;
    if (!NKI_Value_ser(out, x->value.value))
      return false;
    break;
  case NKI_Expr_var:
    if (!cbor_encode_tag(out, 4, 1, 1))
      return false;
    if (!String_ser(out, x->var.name))
      return false;
    break;
  case NKI_Expr_tuple:
    if (!cbor_encode_tag(out, 4, 2, 1))
      return false;
    if (!NKI_Expr_List_ser(out, x->tuple.elements))
      return false;
    break;
  case NKI_Expr_access:
    if (!cbor_encode_tag(out, 4, 3, 2))
      return false;
    if (!NKI_Expr_ser(out, x->access.expr))
      return false;
    if (!NKI_Index_List_ser(out, x->access.indices))
      return false;
    break;
  case NKI_Expr_binOp:
    if (!cbor_encode_tag(out, 4, 4, 3))
      return false;
    if (!NKI_BinOp_ser(out, x->binOp.op))
      return false;
    if (!NKI_Expr_ser(out, x->binOp.left))
      return false;
    if (!NKI_Expr_ser(out, x->binOp.right))
      return false;
    break;
  case NKI_Expr_ifExp:
    if (!cbor_encode_tag(out, 4, 5, 3))
      return false;
    if (!NKI_Expr_ser(out, x->ifExp.test))
      return false;
    if (!NKI_Expr_ser(out, x->ifExp.body))
      return false;
    if (!NKI_Expr_ser(out, x->ifExp.orelse))
      return false;
    break;
  case NKI_Expr_call:
    if (!cbor_encode_tag(out, 4, 6, 3))
      return false;
    if (!NKI_Expr_ser(out, x->call.f))
      return false;
    if (!NKI_Expr_List_ser(out, x->call.args))
      return false;
    if (!NKI_Keyword_List_ser(out, x->call.keywords))
      return false;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Expr_ser(FILE *out, struct NKI_Expr *x) {
  if (!cbor_encode_tag(out, 3, 0, 2))
    return false;
  if (!NKI_Expr__ser(out, x->expr))
    return false;
  if (!Core_Pos_ser(out, x->pos))
    return false;
  return true;
}

bool NKI_Index_ser(FILE *out, struct NKI_Index *x) {
  switch (x->tag) {
  case NKI_Index_coord:
    if (!cbor_encode_tag(out, 5, 0, 1))
      return false;
    if (!NKI_Expr_ser(out, x->coord.i))
      return false;
    break;
  case NKI_Index_slice:
    if (!cbor_encode_tag(out, 5, 1, 3))
      return false;
    if (!NKI_Expr_Option_ser(out, x->slice.l))
      return false;
    if (!NKI_Expr_Option_ser(out, x->slice.u))
      return false;
    if (!NKI_Expr_Option_ser(out, x->slice.step))
      return false;
    break;
  case NKI_Index_ellipsis:
    if (!cbor_encode_tag(out, 5, 2, 0))
      return false;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Keyword_ser(FILE *out, struct NKI_Keyword *x) {
  if (!cbor_encode_tag(out, 6, 0, 2))
    return false;
  if (!String_ser(out, x->name))
    return false;
  if (!NKI_Expr_ser(out, x->expr))
    return false;
  return true;
}

bool NKI_Pattern_ser(FILE *out, struct NKI_Pattern *x) {
  switch (x->tag) {
  case NKI_Pattern_var:
    if (!cbor_encode_tag(out, 7, 0, 1))
      return false;
    if (!String_ser(out, x->var.name))
      return false;
    break;
  case NKI_Pattern_tuple:
    if (!cbor_encode_tag(out, 7, 1, 1))
      return false;
    if (!NKI_Pattern_List_ser(out, x->tuple.xs))
      return false;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Stmt__ser(FILE *out, struct NKI_Stmt_ *x) {
  switch (x->tag) {
  case NKI_Stmt_expr:
    if (!cbor_encode_tag(out, 9, 0, 1))
      return false;
    if (!NKI_Expr_ser(out, x->expr.e))
      return false;
    break;
  case NKI_Stmt_assert:
    if (!cbor_encode_tag(out, 9, 1, 1))
      return false;
    if (!NKI_Expr_ser(out, x->assert.e))
      return false;
    break;
  case NKI_Stmt_ret:
    if (!cbor_encode_tag(out, 9, 2, 1))
      return false;
    if (!NKI_Expr_ser(out, x->ret.e))
      return false;
    break;
  case NKI_Stmt_declare:
    if (!cbor_encode_tag(out, 9, 3, 2))
      return false;
    if (!String_ser(out, x->declare.x))
      return false;
    if (!NKI_Expr_ser(out, x->declare.ty))
      return false;
    break;
  case NKI_Stmt_letM:
    if (!cbor_encode_tag(out, 9, 4, 3))
      return false;
    if (!NKI_Pattern_ser(out, x->letM.p))
      return false;
    if (!NKI_Expr_Option_ser(out, x->letM.ty))
      return false;
    if (!NKI_Expr_ser(out, x->letM.e))
      return false;
    break;
  case NKI_Stmt_setM:
    if (!cbor_encode_tag(out, 9, 5, 3))
      return false;
    if (!NKI_Expr_ser(out, x->setM.x))
      return false;
    if (!NKI_Expr_ser(out, x->setM.e))
      return false;
    if (!cbor_encode_bool(out, x->setM.accum))
      return false;
    break;
  case NKI_Stmt_ifStm:
    if (!cbor_encode_tag(out, 9, 6, 3))
      return false;
    if (!NKI_Expr_ser(out, x->ifStm.e))
      return false;
    if (!NKI_Stmt_List_ser(out, x->ifStm.thn))
      return false;
    if (!NKI_Stmt_List_ser(out, x->ifStm.els))
      return false;
    break;
  case NKI_Stmt_forLoop:
    if (!cbor_encode_tag(out, 9, 7, 3))
      return false;
    if (!NKI_Expr_ser(out, x->forLoop.x))
      return false;
    if (!NKI_Expr_ser(out, x->forLoop.iter))
      return false;
    if (!NKI_Stmt_List_ser(out, x->forLoop.body))
      return false;
    break;
  case NKI_Stmt_breakLoop:
    if (!cbor_encode_tag(out, 9, 8, 0))
      return false;
    break;
  case NKI_Stmt_continueLoop:
    if (!cbor_encode_tag(out, 9, 9, 0))
      return false;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Stmt_ser(FILE *out, struct NKI_Stmt *x) {
  if (!cbor_encode_tag(out, 8, 0, 2))
    return false;
  if (!NKI_Stmt__ser(out, x->stmt))
    return false;
  if (!Core_Pos_ser(out, x->pos))
    return false;
  return true;
}

bool NKI_Param_ser(FILE *out, struct NKI_Param *x) {
  if (!cbor_encode_tag(out, 10, 0, 2))
    return false;
  if (!String_ser(out, x->name))
    return false;
  if (!NKI_Expr_Option_ser(out, x->dflt))
    return false;
  return true;
}

bool NKI_Fun_ser(FILE *out, struct NKI_Fun *x) {
  if (!cbor_encode_tag(out, 11, 0, 5))
    return false;
  if (!String_ser(out, x->name))
    return false;
  if (!String_ser(out, x->file))
    return false;
  if (!cbor_encode_uint(out, x->line))
    return false;
  if (!NKI_Stmt_List_ser(out, x->body))
    return false;
  if (!NKI_Param_List_ser(out, x->args))
    return false;
  return true;
}

bool NKI_Arg_ser(FILE *out, struct NKI_Arg *x) {
  if (!cbor_encode_tag(out, 12, 0, 2))
    return false;
  if (!String_ser(out, x->name))
    return false;
  if (!NKI_Expr_ser(out, x->value))
    return false;
  return true;
}

bool NKI_Kernel_ser(FILE *out, struct NKI_Kernel *x) {
  if (!cbor_encode_tag(out, 13, 0, 4))
    return false;
  if (!String_ser(out, x->entry))
    return false;
  if (!NKI_Fun_List_ser(out, x->funs))
    return false;
  if (!NKI_Arg_List_ser(out, x->args))
    return false;
  if (!NKI_Arg_List_ser(out, x->globals))
    return false;
  return true;
}

bool NKI_Expr_List_ser(FILE *out, struct NKI_Expr_List *x) {
  u64 count = 0;
  for (struct NKI_Expr_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Expr_List *node = x; node; node = node->next)
    if (!NKI_Expr_ser(out, node->expr))
      return false;
  return true;
}

bool NKI_Index_List_ser(FILE *out, struct NKI_Index_List *x) {
  u64 count = 0;
  for (struct NKI_Index_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Index_List *node = x; node; node = node->next)
    if (!NKI_Index_ser(out, node->index))
      return false;
  return true;
}

bool NKI_Keyword_List_ser(FILE *out, struct NKI_Keyword_List *x) {
  u64 count = 0;
  for (struct NKI_Keyword_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Keyword_List *node = x; node; node = node->next)
    if (!NKI_Keyword_ser(out, node->keyword))
      return false;
  return true;
}

bool NKI_Expr_Option_ser(FILE *out, struct NKI_Expr *x) {
  if (!x) {
    return cbor_encode_option(out, false);
  } else {
    return cbor_encode_option(out, true) && NKI_Expr_ser(out, x);
  }
  return true;
}

bool NKI_Pattern_List_ser(FILE *out, struct NKI_Pattern_List *x) {
  u64 count = 0;
  for (struct NKI_Pattern_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Pattern_List *node = x; node; node = node->next)
    if (!NKI_Pattern_ser(out, node->pattern))
      return false;
  return true;
}

bool NKI_Stmt_List_ser(FILE *out, struct NKI_Stmt_List *x) {
  u64 count = 0;
  for (struct NKI_Stmt_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Stmt_List *node = x; node; node = node->next)
    if (!NKI_Stmt_ser(out, node->stmt))
      return false;
  return true;
}

bool NKI_Param_List_ser(FILE *out, struct NKI_Param_List *x) {
  u64 count = 0;
  for (struct NKI_Param_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Param_List *node = x; node; node = node->next)
    if (!NKI_Param_ser(out, node->param))
      return false;
  return true;
}

bool NKI_Fun_List_ser(FILE *out, struct NKI_Fun_List *x) {
  u64 count = 0;
  for (struct NKI_Fun_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Fun_List *node = x; node; node = node->next)
    if (!NKI_Fun_ser(out, node->fun))
      return false;
  return true;
}

bool NKI_Arg_List_ser(FILE *out, struct NKI_Arg_List *x) {
  u64 count = 0;
  for (struct NKI_Arg_List *node = x; node; node = node->next)
    count++;
  if (!cbor_encode_array_start(out, count))
    return false;
  for (struct NKI_Arg_List *node = x; node; node = node->next)
    if (!NKI_Arg_ser(out, node->arg))
      return false;
  return true;
}

bool NKI_Value_des(FILE *in, struct region *region, struct NKI_Value **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 1)
    return false;
  *x = region_alloc(region, sizeof(**x));
  switch (c) {
  case 0:
    if (l != 0)
      return false;
    (*x)->tag = NKI_Value_none;
    break;
  case 1:
    if (l != 1)
      return false;
    if (!Bool_des(in, region, &(*x)->b.value))
      return false;
    (*x)->tag = NKI_Value_bool;
    break;
  case 2:
    if (l != 1)
      return false;
    if (!Int_des(in, region, &(*x)->i.value))
      return false;
    (*x)->tag = NKI_Value_int;
    break;
  case 3:
    if (l != 1)
      return false;
    if (!Float_des(in, region, &(*x)->f.value))
      return false;
    (*x)->tag = NKI_Value_float;
    break;
  case 4:
    if (l != 1)
      return false;
    if (!String_des(in, region, &(*x)->s.value))
      return false;
    (*x)->tag = NKI_Value_string;
    break;
  case 5:
    if (l != 2)
      return false;
    if (!Nat_List_des(in, region, &(*x)->tensor.shape))
      return false;
    if (!String_des(in, region, &(*x)->tensor.dtype))
      return false;
    (*x)->tag = NKI_Value_tensor;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_BinOp_des(FILE *in, struct region *region, enum NKI_BinOp *x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 2)
    return false;
  (void)region;
  switch (c) {
  case 0:
    if (l != 0)
      return false;
    *x = NKI_BinOp_land;
    break;
  case 1:
    if (l != 0)
      return false;
    *x = NKI_BinOp_lor;
    break;
  case 2:
    if (l != 0)
      return false;
    *x = NKI_BinOp_eq;
    break;
  case 3:
    if (l != 0)
      return false;
    *x = NKI_BinOp_ne;
    break;
  case 4:
    if (l != 0)
      return false;
    *x = NKI_BinOp_lt;
    break;
  case 5:
    if (l != 0)
      return false;
    *x = NKI_BinOp_le;
    break;
  case 6:
    if (l != 0)
      return false;
    *x = NKI_BinOp_gt;
    break;
  case 7:
    if (l != 0)
      return false;
    *x = NKI_BinOp_ge;
    break;
  case 8:
    if (l != 0)
      return false;
    *x = NKI_BinOp_add;
    break;
  case 9:
    if (l != 0)
      return false;
    *x = NKI_BinOp_sub;
    break;
  case 10:
    if (l != 0)
      return false;
    *x = NKI_BinOp_mul;
    break;
  case 11:
    if (l != 0)
      return false;
    *x = NKI_BinOp_div;
    break;
  case 12:
    if (l != 0)
      return false;
    *x = NKI_BinOp_mod;
    break;
  case 13:
    if (l != 0)
      return false;
    *x = NKI_BinOp_pow;
    break;
  case 14:
    if (l != 0)
      return false;
    *x = NKI_BinOp_floor;
    break;
  case 15:
    if (l != 0)
      return false;
    *x = NKI_BinOp_lshift;
    break;
  case 16:
    if (l != 0)
      return false;
    *x = NKI_BinOp_rshift;
    break;
  case 17:
    if (l != 0)
      return false;
    *x = NKI_BinOp_or;
    break;
  case 18:
    if (l != 0)
      return false;
    *x = NKI_BinOp_xor;
    break;
  case 19:
    if (l != 0)
      return false;
    *x = NKI_BinOp_and;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Expr__des(FILE *in, struct region *region, struct NKI_Expr_ **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 4)
    return false;
  *x = region_alloc(region, sizeof(**x));
  switch (c) {
  case 0:
    if (l != 1)
      return false;
    if (!NKI_Value_des(in, region, &(*x)->value.value))
      return false;
    (*x)->tag = NKI_Expr_value;
    break;
  case 1:
    if (l != 1)
      return false;
    if (!String_des(in, region, &(*x)->var.name))
      return false;
    (*x)->tag = NKI_Expr_var;
    break;
  case 2:
    if (l != 1)
      return false;
    if (!NKI_Expr_List_des(in, region, &(*x)->tuple.elements))
      return false;
    (*x)->tag = NKI_Expr_tuple;
    break;
  case 3:
    if (l != 2)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->access.expr))
      return false;
    if (!NKI_Index_List_des(in, region, &(*x)->access.indices))
      return false;
    (*x)->tag = NKI_Expr_access;
    break;
  case 4:
    if (l != 3)
      return false;
    if (!NKI_BinOp_des(in, region, &(*x)->binOp.op))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->binOp.left))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->binOp.right))
      return false;
    (*x)->tag = NKI_Expr_binOp;
    break;
  case 5:
    if (l != 3)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->ifExp.test))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->ifExp.body))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->ifExp.orelse))
      return false;
    (*x)->tag = NKI_Expr_ifExp;
    break;
  case 6:
    if (l != 3)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->call.f))
      return false;
    if (!NKI_Expr_List_des(in, region, &(*x)->call.args))
      return false;
    if (!NKI_Keyword_List_des(in, region, &(*x)->call.keywords))
      return false;
    (*x)->tag = NKI_Expr_call;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Expr_des(FILE *in, struct region *region, struct NKI_Expr **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 3 || c != 0 || l != 2)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!NKI_Expr__des(in, region, &(*x)->expr))
    return false;
  if (!Core_Pos_des(in, region, &(*x)->pos))
    return false;
  return true;
}

bool NKI_Index_des(FILE *in, struct region *region, struct NKI_Index **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 5)
    return false;
  *x = region_alloc(region, sizeof(**x));
  switch (c) {
  case 0:
    if (l != 1)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->coord.i))
      return false;
    (*x)->tag = NKI_Index_coord;
    break;
  case 1:
    if (l != 3)
      return false;
    if (!NKI_Expr_Option_des(in, region, &(*x)->slice.l))
      return false;
    if (!NKI_Expr_Option_des(in, region, &(*x)->slice.u))
      return false;
    if (!NKI_Expr_Option_des(in, region, &(*x)->slice.step))
      return false;
    (*x)->tag = NKI_Index_slice;
    break;
  case 2:
    if (l != 0)
      return false;
    (*x)->tag = NKI_Index_ellipsis;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Keyword_des(FILE *in, struct region *region, struct NKI_Keyword **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 6 || c != 0 || l != 2)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!String_des(in, region, &(*x)->name))
    return false;
  if (!NKI_Expr_des(in, region, &(*x)->expr))
    return false;
  return true;
}

bool NKI_Pattern_des(FILE *in, struct region *region, struct NKI_Pattern **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 7)
    return false;
  *x = region_alloc(region, sizeof(**x));
  switch (c) {
  case 0:
    if (l != 1)
      return false;
    if (!String_des(in, region, &(*x)->var.name))
      return false;
    (*x)->tag = NKI_Pattern_var;
    break;
  case 1:
    if (l != 1)
      return false;
    if (!NKI_Pattern_List_des(in, region, &(*x)->tuple.xs))
      return false;
    (*x)->tag = NKI_Pattern_tuple;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Stmt__des(FILE *in, struct region *region, struct NKI_Stmt_ **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 9)
    return false;
  *x = region_alloc(region, sizeof(**x));
  switch (c) {
  case 0:
    if (l != 1)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->expr.e))
      return false;
    (*x)->tag = NKI_Stmt_expr;
    break;
  case 1:
    if (l != 1)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->assert.e))
      return false;
    (*x)->tag = NKI_Stmt_assert;
    break;
  case 2:
    if (l != 1)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->ret.e))
      return false;
    (*x)->tag = NKI_Stmt_ret;
    break;
  case 3:
    if (l != 2)
      return false;
    if (!String_des(in, region, &(*x)->declare.x))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->declare.ty))
      return false;
    (*x)->tag = NKI_Stmt_declare;
    break;
  case 4:
    if (l != 3)
      return false;
    if (!NKI_Pattern_des(in, region, &(*x)->letM.p))
      return false;
    if (!NKI_Expr_Option_des(in, region, &(*x)->letM.ty))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->letM.e))
      return false;
    (*x)->tag = NKI_Stmt_letM;
    break;
  case 5:
    if (l != 3)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->setM.x))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->setM.e))
      return false;
    if (!Bool_des(in, region, &(*x)->setM.accum))
      return false;
    (*x)->tag = NKI_Stmt_setM;
    break;
  case 6:
    if (l != 3)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->ifStm.e))
      return false;
    if (!NKI_Stmt_List_des(in, region, &(*x)->ifStm.thn))
      return false;
    if (!NKI_Stmt_List_des(in, region, &(*x)->ifStm.els))
      return false;
    (*x)->tag = NKI_Stmt_ifStm;
    break;
  case 7:
    if (l != 3)
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->forLoop.x))
      return false;
    if (!NKI_Expr_des(in, region, &(*x)->forLoop.iter))
      return false;
    if (!NKI_Stmt_List_des(in, region, &(*x)->forLoop.body))
      return false;
    (*x)->tag = NKI_Stmt_forLoop;
    break;
  case 8:
    if (l != 0)
      return false;
    (*x)->tag = NKI_Stmt_breakLoop;
    break;
  case 9:
    if (l != 0)
      return false;
    (*x)->tag = NKI_Stmt_continueLoop;
    break;
  default:
    return false;
  }
  return true;
}

bool NKI_Stmt_des(FILE *in, struct region *region, struct NKI_Stmt **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 8 || c != 0 || l != 2)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!NKI_Stmt__des(in, region, &(*x)->stmt))
    return false;
  if (!Core_Pos_des(in, region, &(*x)->pos))
    return false;
  return true;
}

bool NKI_Param_des(FILE *in, struct region *region, struct NKI_Param **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 10 || c != 0 || l != 2)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!String_des(in, region, &(*x)->name))
    return false;
  if (!NKI_Expr_Option_des(in, region, &(*x)->dflt))
    return false;
  return true;
}

bool NKI_Fun_des(FILE *in, struct region *region, struct NKI_Fun **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 11 || c != 0 || l != 5)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!String_des(in, region, &(*x)->name))
    return false;
  if (!String_des(in, region, &(*x)->file))
    return false;
  if (!Nat_des(in, region, &(*x)->line))
    return false;
  if (!NKI_Stmt_List_des(in, region, &(*x)->body))
    return false;
  if (!NKI_Param_List_des(in, region, &(*x)->args))
    return false;
  return true;
}

bool NKI_Arg_des(FILE *in, struct region *region, struct NKI_Arg **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 12 || c != 0 || l != 2)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!String_des(in, region, &(*x)->name))
    return false;
  if (!NKI_Expr_des(in, region, &(*x)->value))
    return false;
  return true;
}

bool NKI_Kernel_des(FILE *in, struct region *region, struct NKI_Kernel **x) {
  u8 t, c, l;
  if (!cbor_decode_tag(in, &t, &c, &l))
    return false;
  if (t != 13 || c != 0 || l != 4)
    return false;
  *x = region_alloc(region, sizeof(**x));
  if (!String_des(in, region, &(*x)->entry))
    return false;
  if (!NKI_Fun_List_des(in, region, &(*x)->funs))
    return false;
  if (!NKI_Arg_List_des(in, region, &(*x)->args))
    return false;
  if (!NKI_Arg_List_des(in, region, &(*x)->globals))
    return false;
  return true;
}

bool NKI_Expr_List_des(FILE *in, struct region *region,
                       struct NKI_Expr_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Expr_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Expr_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Expr_des(in, region, &node->expr))
      return false;
  }
  return true;
}

bool NKI_Index_List_des(FILE *in, struct region *region,
                        struct NKI_Index_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Index_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Index_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Index_des(in, region, &node->index))
      return false;
  }
  return true;
}

bool NKI_Keyword_List_des(FILE *in, struct region *region,
                          struct NKI_Keyword_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Keyword_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Keyword_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Keyword_des(in, region, &node->keyword))
      return false;
  }
  return true;
}

bool NKI_Expr_Option_des(FILE *in, struct region *region, struct NKI_Expr **x) {
  bool isSome;
  if (!cbor_decode_option(in, &isSome))
    return false;
  if (!isSome)
    *x = 0;
  else
    return NKI_Expr_des(in, region, x);
  return true;
}

bool NKI_Pattern_List_des(FILE *in, struct region *region,
                          struct NKI_Pattern_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Pattern_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Pattern_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Pattern_des(in, region, &node->pattern))
      return false;
  }
  return true;
}

bool NKI_Stmt_List_des(FILE *in, struct region *region,
                       struct NKI_Stmt_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Stmt_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Stmt_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Stmt_des(in, region, &node->stmt))
      return false;
  }
  return true;
}

bool NKI_Param_List_des(FILE *in, struct region *region,
                        struct NKI_Param_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Param_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Param_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Param_des(in, region, &node->param))
      return false;
  }
  return true;
}

bool NKI_Fun_List_des(FILE *in, struct region *region,
                      struct NKI_Fun_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Fun_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Fun_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Fun_des(in, region, &node->fun))
      return false;
  }
  return true;
}

bool NKI_Arg_List_des(FILE *in, struct region *region,
                      struct NKI_Arg_List **x) {
  u64 count = 0;
  if (!cbor_decode_array_start(in, &count))
    return false;
  struct NKI_Arg_List *current = *x = NULL;
  for (; count > 0; count--) {
    struct NKI_Arg_List *node = region_alloc(region, sizeof(*node));
    node->next = NULL;
    if (!current) {
      *x = current = node;
    } else {
      current->next = node;
      current = node;
    }
    if (!NKI_Arg_des(in, region, &node->arg))
      return false;
  }
  return true;
}
