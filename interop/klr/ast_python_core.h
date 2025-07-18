/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once

// This file is automatically generated from KLR.
// Manual edits to this file will be overwritten.

#include "stdc.h"
#include "region.h"
#include "ast_common.h"

// KLR.Python Abstract Syntax

struct Python_Const {
  enum Python_Const_Tag {
    Python_Const_none = 1,
    Python_Const_bool,
    Python_Const_int,
    Python_Const_float,
    Python_Const_string,
    Python_Const_ellipsis,
    Python_Const_tensor,
  } tag;
  union {
    struct Python_Const_bool {
      bool value;
    } b;
    struct Python_Const_int {
      i32 value;
    } i;
    struct Python_Const_float {
      f32 value;
    } f;
    struct Python_Const_string {
      char *value;
    } s;
    struct Python_Const_tensor {
      struct Nat_List *shape;
      char *dtype;
    } tensor;
  };
};

enum Python_Ctx {
  Python_Ctx_load = 1,
  Python_Ctx_store,
  Python_Ctx_del,
};

enum Python_BoolOp {
  Python_BoolOp_land = 1,
  Python_BoolOp_lor,
};

enum Python_CmpOp {
  Python_CmpOp_eq = 1,
  Python_CmpOp_ne,
  Python_CmpOp_lt,
  Python_CmpOp_le,
  Python_CmpOp_gt,
  Python_CmpOp_ge,
  Python_CmpOp_is,
  Python_CmpOp_isNot,
  Python_CmpOp_isIn,
  Python_CmpOp_notIn,
};

enum Python_UnaryOp {
  Python_UnaryOp_invert = 1,
  Python_UnaryOp_not,
  Python_UnaryOp_uadd,
  Python_UnaryOp_usub,
};

enum Python_BinOp {
  Python_BinOp_add = 1,
  Python_BinOp_sub,
  Python_BinOp_mul,
  Python_BinOp_matmul,
  Python_BinOp_div,
  Python_BinOp_mod,
  Python_BinOp_pow,
  Python_BinOp_lshift,
  Python_BinOp_rshift,
  Python_BinOp_or,
  Python_BinOp_xor,
  Python_BinOp_and,
  Python_BinOp_floor,
};

struct Python_Expr_ {
  enum Python_Expr_Tag {
    Python_Expr_const = 1,
    Python_Expr_name,
    Python_Expr_attr,
    Python_Expr_tuple,
    Python_Expr_list,
    Python_Expr_subscript,
    Python_Expr_slice,
    Python_Expr_boolOp,
    Python_Expr_binOp,
    Python_Expr_unaryOp,
    Python_Expr_compare,
    Python_Expr_ifExp,
    Python_Expr_call,
  } tag;
  union {
    struct Python_Expr_const {
      struct Python_Const *value;
    } c;
    struct Python_Expr_name {
      char *id;
      enum Python_Ctx ctx;
    } name;
    struct Python_Expr_attr {
      struct Python_Expr *value;
      char *id;
      enum Python_Ctx ctx;
    } attr;
    struct Python_Expr_tuple {
      struct Python_Expr_List *xs;
      enum Python_Ctx ctx;
    } tuple;
    struct Python_Expr_list {
      struct Python_Expr_List *xs;
      enum Python_Ctx ctx;
    } list;
    struct Python_Expr_subscript {
      struct Python_Expr *tensor;
      struct Python_Expr *index;
      enum Python_Ctx ctx;
    } subscript;
    struct Python_Expr_slice {
      struct Python_Expr *l;
      struct Python_Expr *u;
      struct Python_Expr *step;
    } slice;
    struct Python_Expr_boolOp {
      enum Python_BoolOp op;
      struct Python_Expr_List *values;
    } boolOp;
    struct Python_Expr_binOp {
      enum Python_BinOp op;
      struct Python_Expr *left;
      struct Python_Expr *right;
    } binOp;
    struct Python_Expr_unaryOp {
      enum Python_UnaryOp op;
      struct Python_Expr *operand;
    } unaryOp;
    struct Python_Expr_compare {
      struct Python_Expr *left;
      struct Python_CmpOp_List *ops;
      struct Python_Expr_List *comparators;
    } compare;
    struct Python_Expr_ifExp {
      struct Python_Expr *test;
      struct Python_Expr *body;
      struct Python_Expr *orelse;
    } ifExp;
    struct Python_Expr_call {
      struct Python_Expr *f;
      struct Python_Expr_List *args;
      struct Python_Keyword_List *keywords;
    } call;
  };
};

struct Python_Expr {
  struct Python_Expr_ *expr;
  struct Core_Pos *pos;
};

struct Python_Keyword {
  char *id;
  struct Python_Expr *value;
  struct Core_Pos *pos;
};

struct Python_Stmt_ {
  enum Python_Stmt_Tag {
    Python_Stmt_pass = 1,
    Python_Stmt_expr,
    Python_Stmt_assert,
    Python_Stmt_ret,
    Python_Stmt_assign,
    Python_Stmt_augAssign,
    Python_Stmt_annAssign,
    Python_Stmt_ifStm,
    Python_Stmt_forLoop,
    Python_Stmt_breakLoop,
    Python_Stmt_continueLoop,
  } tag;
  union {
    struct Python_Stmt_expr {
      struct Python_Expr *e;
    } expr;
    struct Python_Stmt_assert {
      struct Python_Expr *e;
    } assert;
    struct Python_Stmt_ret {
      struct Python_Expr *e;
    } ret;
    struct Python_Stmt_assign {
      struct Python_Expr_List *xs;
      struct Python_Expr *e;
    } assign;
    struct Python_Stmt_augAssign {
      struct Python_Expr *x;
      enum Python_BinOp op;
      struct Python_Expr *e;
    } augAssign;
    struct Python_Stmt_annAssign {
      struct Python_Expr *x;
      struct Python_Expr *annotation;
      struct Python_Expr *value;
    } annAssign;
    struct Python_Stmt_ifStm {
      struct Python_Expr *e;
      struct Python_Stmt_List *thn;
      struct Python_Stmt_List *els;
    } ifStm;
    struct Python_Stmt_forLoop {
      struct Python_Expr *x;
      struct Python_Expr *iter;
      struct Python_Stmt_List *body;
      struct Python_Stmt_List *orelse;
    } forLoop;
  };
};

struct Python_Stmt {
  struct Python_Stmt_ *stmt;
  struct Core_Pos *pos;
};

struct Python_Args {
  struct String_List *posonlyargs;
  struct String_List *args;
  struct Python_Expr_List *defaults;
  char *vararg;
  struct String_List *kwonlyargs;
  struct Python_Keyword_List *kw_defaults;
  char *kwarg;
};

struct Python_Fun {
  char *name;
  u32 line;
  char *source;
  struct Python_Args *args;
  struct Python_Stmt_List *body;
};

struct Python_Kernel {
  char *entry;
  struct Python_Fun_List *funcs;
  struct Python_Expr_List *args;
  struct Python_Keyword_List *kwargs;
  struct Python_Keyword_List *globals;
  struct String_List *undefinedSymbols;
};

struct Python_Expr_List {
  struct Python_Expr_List *next;
  struct Python_Expr *expr;
};

struct Python_CmpOp_List {
  struct Python_CmpOp_List *next;
  enum Python_CmpOp cmpop;
};

struct Python_Keyword_List {
  struct Python_Keyword_List *next;
  struct Python_Keyword *keyword;
};

struct Python_Stmt_List {
  struct Python_Stmt_List *next;
  struct Python_Stmt *stmt;
};

struct Python_Fun_List {
  struct Python_Fun_List *next;
  struct Python_Fun *fun;
};

static inline struct Python_Expr *
mkPython_Expr_const(struct Python_Const *value, struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_const;
  res->expr->c.value = value;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_name(char *id, enum Python_Ctx ctx, struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_name;
  res->expr->name.id = id;
  res->expr->name.ctx = ctx;
  return res;
}

static inline struct Python_Expr *mkPython_Expr_attr(struct Python_Expr *value,
                                                     char *id,
                                                     enum Python_Ctx ctx,
                                                     struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_attr;
  res->expr->attr.value = value;
  res->expr->attr.id = id;
  res->expr->attr.ctx = ctx;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_tuple(struct Python_Expr_List *xs, enum Python_Ctx ctx,
                    struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_tuple;
  res->expr->tuple.xs = xs;
  res->expr->tuple.ctx = ctx;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_list(struct Python_Expr_List *xs, enum Python_Ctx ctx,
                   struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_list;
  res->expr->list.xs = xs;
  res->expr->list.ctx = ctx;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_subscript(struct Python_Expr *tensor, struct Python_Expr *index,
                        enum Python_Ctx ctx, struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_subscript;
  res->expr->subscript.tensor = tensor;
  res->expr->subscript.index = index;
  res->expr->subscript.ctx = ctx;
  return res;
}

static inline struct Python_Expr *mkPython_Expr_slice(struct Python_Expr *l,
                                                      struct Python_Expr *u,
                                                      struct Python_Expr *step,
                                                      struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_slice;
  res->expr->slice.l = l;
  res->expr->slice.u = u;
  res->expr->slice.step = step;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_boolOp(enum Python_BoolOp op, struct Python_Expr_List *values,
                     struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_boolOp;
  res->expr->boolOp.op = op;
  res->expr->boolOp.values = values;
  return res;
}

static inline struct Python_Expr *mkPython_Expr_binOp(enum Python_BinOp op,
                                                      struct Python_Expr *left,
                                                      struct Python_Expr *right,
                                                      struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_binOp;
  res->expr->binOp.op = op;
  res->expr->binOp.left = left;
  res->expr->binOp.right = right;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_unaryOp(enum Python_UnaryOp op, struct Python_Expr *operand,
                      struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_unaryOp;
  res->expr->unaryOp.op = op;
  res->expr->unaryOp.operand = operand;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_compare(struct Python_Expr *left, struct Python_CmpOp_List *ops,
                      struct Python_Expr_List *comparators,
                      struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_compare;
  res->expr->compare.left = left;
  res->expr->compare.ops = ops;
  res->expr->compare.comparators = comparators;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_ifExp(struct Python_Expr *test, struct Python_Expr *body,
                    struct Python_Expr *orelse, struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_ifExp;
  res->expr->ifExp.test = test;
  res->expr->ifExp.body = body;
  res->expr->ifExp.orelse = orelse;
  return res;
}

static inline struct Python_Expr *
mkPython_Expr_call(struct Python_Expr *f, struct Python_Expr_List *args,
                   struct Python_Keyword_List *keywords,
                   struct region *region) {
  struct Python_Expr *res = region_alloc(region, sizeof(*res));
  res->expr = region_alloc(region, sizeof(*res->expr));
  res->expr->tag = Python_Expr_call;
  res->expr->call.f = f;
  res->expr->call.args = args;
  res->expr->call.keywords = keywords;
  return res;
}

static inline struct Python_Stmt *mkPython_Stmt_pass(struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_pass;
  return res;
}

static inline struct Python_Stmt *mkPython_Stmt_expr(struct Python_Expr *e,
                                                     struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_expr;
  res->stmt->expr.e = e;
  return res;
}

static inline struct Python_Stmt *mkPython_Stmt_assert(struct Python_Expr *e,
                                                       struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_assert;
  res->stmt->assert.e = e;
  return res;
}

static inline struct Python_Stmt *mkPython_Stmt_ret(struct Python_Expr *e,
                                                    struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_ret;
  res->stmt->ret.e = e;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_assign(struct Python_Expr_List *xs, struct Python_Expr *e,
                     struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_assign;
  res->stmt->assign.xs = xs;
  res->stmt->assign.e = e;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_augAssign(struct Python_Expr *x, enum Python_BinOp op,
                        struct Python_Expr *e, struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_augAssign;
  res->stmt->augAssign.x = x;
  res->stmt->augAssign.op = op;
  res->stmt->augAssign.e = e;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_annAssign(struct Python_Expr *x, struct Python_Expr *annotation,
                        struct Python_Expr *value, struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_annAssign;
  res->stmt->annAssign.x = x;
  res->stmt->annAssign.annotation = annotation;
  res->stmt->annAssign.value = value;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_ifStm(struct Python_Expr *e, struct Python_Stmt_List *thn,
                    struct Python_Stmt_List *els, struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_ifStm;
  res->stmt->ifStm.e = e;
  res->stmt->ifStm.thn = thn;
  res->stmt->ifStm.els = els;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_forLoop(struct Python_Expr *x, struct Python_Expr *iter,
                      struct Python_Stmt_List *body,
                      struct Python_Stmt_List *orelse, struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_forLoop;
  res->stmt->forLoop.x = x;
  res->stmt->forLoop.iter = iter;
  res->stmt->forLoop.body = body;
  res->stmt->forLoop.orelse = orelse;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_breakLoop(struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_breakLoop;
  return res;
}

static inline struct Python_Stmt *
mkPython_Stmt_continueLoop(struct region *region) {
  struct Python_Stmt *res = region_alloc(region, sizeof(*res));
  res->stmt = region_alloc(region, sizeof(*res->stmt));
  res->stmt->tag = Python_Stmt_continueLoop;
  return res;
}
