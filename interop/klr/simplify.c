/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Claude
*/

// NOTE: This code was written by Q
// TODO: Positions are not reported in errors

#include "frontend.h"
#include "ast_python_core.h"
#include "ast_nki.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Error handling structure
struct SimplifyError {
  char *message;
  struct NKI_Pos *pos;
};

// Result type for simplification operations
struct SimplifyResult {
  bool success;
  struct SimplifyError error;
  union {
    struct NKI_Expr *expr;
    struct NKI_Stmt_List *stmts;
    struct NKI_Kernel *kernel;
    enum NKI_BinOp binop;
    struct NKI_Expr_List *expr_list;
    struct NKI_Index_List *index_list;
    struct NKI_Keyword_List *keyword_list;
    struct NKI_Param_List *param_list;
    struct NKI_Arg_List *arg_list;
    struct NKI_Fun *fun;
    u32 nat;
    struct Nat_List *nat_list;
  } value;
};

// Helper function to create error result
static struct SimplifyResult make_error(const char *message,
                                        struct NKI_Pos *pos) {
  struct SimplifyResult result = {0};
  result.success = false;
  result.error.message = (char *)message; // Just store the pointer, don't duplicate
  result.error.pos = pos;
  return result;
}

// Helper function to create success result
static struct SimplifyResult make_success_expr(struct NKI_Expr *expr) {
  struct SimplifyResult result = {0};
  result.success = true;
  result.value.expr = expr;
  return result;
}

static struct SimplifyResult make_success_binop(enum NKI_BinOp op) {
  struct SimplifyResult result = {0};
  result.success = true;
  result.value.binop = op;
  return result;
}

static struct SimplifyResult make_success_nat(u32 nat) {
  struct SimplifyResult result = {0};
  result.success = true;
  result.value.nat = nat;
  return result;
}

// Convert Python constant to NKI value
static struct NKI_Value *value_convert(struct Python_Const *c,
                                       struct region *region) {
  struct NKI_Value *result = region_alloc(region, sizeof(*result));
  if (!result)
    return NULL;

  if (!c) {
    result->tag = NKI_Value_none;
    return result;
  }

  switch (c->tag) {
  case Python_Const_none:
    result->tag = NKI_Value_none;
    break;
  case Python_Const_bool:
    result->tag = NKI_Value_bool;
    result->b.value = c->b.value;
    break;
  case Python_Const_int:
    result->tag = NKI_Value_int;
    result->i.value = c->i.value;
    break;
  case Python_Const_float:
    result->tag = NKI_Value_float;
    result->f.value = c->f.value;
    break;
  case Python_Const_string:
    result->tag = NKI_Value_string;
    result->s.value = c->s.value;
    break;
  case Python_Const_ellipsis:
    result->tag = NKI_Value_ellipsis;
    break;
  }
  return result;
}

// Convert Python boolean operator to NKI binary operator
static enum NKI_BinOp boolOp_convert(enum Python_BoolOp op) {
  switch (op) {
  case Python_BoolOp_land:
    return NKI_BinOp_land;
  case Python_BoolOp_lor:
    return NKI_BinOp_lor;
  default:
    return NKI_BinOp_land; // fallback
  }
}
// Convert Python comparison operator to NKI binary operator
static struct SimplifyResult cmpOp_convert(enum Python_CmpOp op) {
  switch (op) {
  case Python_CmpOp_eq:
    return make_success_binop(NKI_BinOp_eq);
  case Python_CmpOp_ne:
    return make_success_binop(NKI_BinOp_ne);
  case Python_CmpOp_lt:
    return make_success_binop(NKI_BinOp_lt);
  case Python_CmpOp_le:
    return make_success_binop(NKI_BinOp_le);
  case Python_CmpOp_gt:
    return make_success_binop(NKI_BinOp_gt);
  case Python_CmpOp_ge:
    return make_success_binop(NKI_BinOp_ge);
  case Python_CmpOp_is:
  case Python_CmpOp_isNot:
    return make_error("the is operator is not supported in NKI, use ==", NULL);
  case Python_CmpOp_isIn:
  case Python_CmpOp_notIn:
    return make_error("the in operator is not supported in NKI", NULL);
  default:
    return make_error("unknown comparison operator", NULL);
  }
}

// Convert Python unary operator to function call expression
static struct SimplifyResult unaryOp_convert(enum Python_UnaryOp op,
                                             struct NKI_Expr *operand,
                                             struct region *region) {
  struct NKI_Expr *result;
  struct NKI_Expr_List *args;
  struct NKI_Expr *func_var;

  switch (op) {
  case Python_UnaryOp_invert:
    // Create function call: invert(operand)
    func_var = mkNKI_Expr_var("invert", region);
    args = region_alloc(region, sizeof(*args));
    args->expr = operand;
    args->next = NULL;

    result = mkNKI_Expr_call(func_var, args, NULL, region);
    return make_success_expr(result);

  case Python_UnaryOp_not:
    // Create function call: not(operand)
    func_var = mkNKI_Expr_var("not", region);
    args = region_alloc(region, sizeof(*args));
    args->expr = operand;
    args->next = NULL;

    result = mkNKI_Expr_call(func_var, args, NULL, region);
    return make_success_expr(result);

  case Python_UnaryOp_uadd:
    // Return the operand unchanged
    return make_success_expr(operand);

  case Python_UnaryOp_usub:
    // Create function call: negate(operand)
    func_var = mkNKI_Expr_var("negate", region);
    args = region_alloc(region, sizeof(*args));
    args->expr = operand;
    args->next = NULL;

    result = mkNKI_Expr_call(func_var, args, NULL, region);
    return make_success_expr(result);

  default:
    return make_error("unknown unary operator", NULL);
  }
}

// Convert Python binary operator to NKI binary operator
static struct SimplifyResult binOp_convert(enum Python_BinOp op) {
  switch (op) {
  case Python_BinOp_add:
    return make_success_binop(NKI_BinOp_add);
  case Python_BinOp_sub:
    return make_success_binop(NKI_BinOp_sub);
  case Python_BinOp_mul:
    return make_success_binop(NKI_BinOp_mul);
  case Python_BinOp_matmul:
    return make_error("the matmul operator is not supported in NKI", NULL);
  case Python_BinOp_div:
    return make_success_binop(NKI_BinOp_div);
  case Python_BinOp_mod:
    return make_success_binop(NKI_BinOp_mod);
  case Python_BinOp_pow:
    return make_success_binop(NKI_BinOp_pow);
  case Python_BinOp_lshift:
    return make_success_binop(NKI_BinOp_lshift);
  case Python_BinOp_rshift:
    return make_success_binop(NKI_BinOp_rshift);
  case Python_BinOp_or:
    return make_success_binop(NKI_BinOp_or);
  case Python_BinOp_xor:
    return make_success_binop(NKI_BinOp_xor);
  case Python_BinOp_and:
    return make_success_binop(NKI_BinOp_and);
  case Python_BinOp_floor:
    return make_success_binop(NKI_BinOp_floor);
  default:
    return make_error("unknown binary operator", NULL);
  }
}

// Forward declarations
static struct SimplifyResult expr_convert(struct Python_Expr *e, struct region *region);
static struct SimplifyResult exprs_convert(struct Python_Expr_List *es, struct region *region);

// Handle boolean operations (land/lor) on a list of expressions
static struct SimplifyResult booleanOp_convert(enum NKI_BinOp op,
                                               struct NKI_Expr_List *exprs,
                                               struct region *region) {
  if (!exprs) {
    return make_error("invalid boolean expression", NULL);
  }

  if (!exprs->next) {
    // Single expression, return it directly
    return make_success_expr(exprs->expr);
  }

  // Multiple expressions, create nested binary operations
  struct NKI_Expr *left = exprs->expr;
  struct NKI_Expr_List *rest = exprs->next;

  // Recursively handle the rest
  struct SimplifyResult rest_result = booleanOp_convert(op, rest, region);
  if (!rest_result.success) {
    return rest_result;
  }

  struct NKI_Expr *result =
      mkNKI_Expr_binOp(op, left, rest_result.value.expr, region);
  return make_success_expr(result);
}

// Handle comparison operations
static struct SimplifyResult compare_convert(struct NKI_Expr *left,
                                             struct Python_CmpOp_List *ops,
                                             struct NKI_Expr_List *comparators,
                                             struct region *region) {
  if (!ops || !comparators) {
    return make_error("invalid comparison expression", NULL);
  }

  if (!ops->next && !comparators->next) {
    // Single comparison: left op right
    struct SimplifyResult op_result = cmpOp_convert(ops->cmpop);
    if (!op_result.success) {
      return op_result;
    }

    struct NKI_Expr *result = mkNKI_Expr_binOp(op_result.value.binop, left,
                                               comparators->expr, region);
    return make_success_expr(result);
  }

  if (ops->next && comparators->next) {
    // Multiple comparisons: left op1 middle op2 right...
    struct SimplifyResult op_result = cmpOp_convert(ops->cmpop);
    if (!op_result.success) {
      return op_result;
    }

    // Recursively handle the rest
    struct SimplifyResult rest_result = compare_convert(
        comparators->expr, ops->next, comparators->next, region);
    if (!rest_result.success) {
      return rest_result;
    }

    struct NKI_Expr *result = mkNKI_Expr_binOp(op_result.value.binop, left,
                                               rest_result.value.expr, region);
    return make_success_expr(result);
  }

  return make_error("invalid comparison expression", NULL);
}

// Convert natural number from Python expression
static struct SimplifyResult nat_convert(struct Python_Expr_ *e) {
  if (e->tag == Python_Expr_const && e->c.value->tag == Python_Const_int) {
    i32 val = e->c.value->i.value;
    if (val >= 0) {
      return make_success_nat((u32)val);
    }
  }
  return make_error("expecting positive integer", NULL);
}

// Convert shape (list of natural numbers)
static struct SimplifyResult shape_convert(struct Python_Expr_List *exprs,
                                           struct region *region) {
  if (!exprs) {
    struct SimplifyResult result = {0};
    result.success = true;
    result.value.nat_list = NULL;
    return result;
  }

  struct SimplifyResult nat_result = nat_convert(exprs->expr->expr);
  if (!nat_result.success) {
    return nat_result;
  }

  struct SimplifyResult rest_result = shape_convert(exprs->next, region);
  if (!rest_result.success) {
    return rest_result;
  }

  struct Nat_List *result = region_alloc(region, sizeof(*result));
  result->nat = nat_result.value.nat;
  result->next = rest_result.value.nat_list;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.nat_list = result;
  return final_result;
}

// Forward declarations for mutual recursion
static struct SimplifyResult expr_prime_convert(struct Python_Expr_ *e, struct region *region);
static struct SimplifyResult indexes_convert(struct Python_Expr *e, struct region *region);
static struct SimplifyResult keywords_convert(struct Python_Keyword_List *ks, struct region *region);

// Convert Python expression to NKI expression
static struct SimplifyResult expr_convert(struct Python_Expr *e,
                                          struct region *region) {
  if (!e || !e->expr || !e->pos) {
    return make_error("invalid expression", NULL);
  }

  struct SimplifyResult expr_result = expr_prime_convert(e->expr, region);
  if (!expr_result.success) {
    return expr_result;
  }

  struct NKI_Expr *result = region_alloc(region, sizeof(*result));
  result->expr = expr_result.value.expr->expr;
  result->pos = e->pos;

  return make_success_expr(result);
}

// Convert list of Python expressions to list of NKI expressions
static struct SimplifyResult exprs_convert(struct Python_Expr_List *es,
                                           struct region *region) {
  if (!es) {
    struct SimplifyResult result = {0};
    result.success = true;
    result.value.expr_list = NULL;
    return result;
  }

  struct SimplifyResult expr_result = expr_convert(es->expr, region);
  if (!expr_result.success) {
    return expr_result;
  }

  struct SimplifyResult rest_result = exprs_convert(es->next, region);
  if (!rest_result.success) {
    return rest_result;
  }

  struct NKI_Expr_List *result = region_alloc(region, sizeof(*result));
  result->expr = expr_result.value.expr;
  result->next = rest_result.value.expr_list;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.expr_list = result;
  return final_result;
}

// Convert Python expression body to NKI expression body
static struct SimplifyResult expr_prime_convert(struct Python_Expr_ *e,
                                                struct region *region) {
  if (!e) {
    return make_error("invalid expression", NULL);
  }

  struct NKI_Expr *result;

  switch (e->tag) {
  case Python_Expr_const: {
    struct NKI_Value *val = value_convert(e->c.value, region);
    result = mkNKI_Expr_value(val, region);
    break;
  }

  case Python_Expr_tensor: {
    struct SimplifyResult shape_result = shape_convert(e->tensor.shape, region);
    if (!shape_result.success) {
      return shape_result;
    }

    struct NKI_Value *tensor_val = region_alloc(region, sizeof(*tensor_val));
    tensor_val->tag = NKI_Value_tensor;
    tensor_val->tensor.shape = shape_result.value.nat_list;
    tensor_val->tensor.dtype = e->tensor.dtype;

    result = mkNKI_Expr_value(tensor_val, region);
    break;
  }

  case Python_Expr_name: {
    result = mkNKI_Expr_var(e->name.id, region);
    break;
  }

  case Python_Expr_attr: {
    struct SimplifyResult base_result = expr_convert(e->attr.value, region);
    if (!base_result.success) {
      return base_result;
    }

    // Check if base is a variable, if so concatenate names
    if (base_result.value.expr->expr->tag == NKI_Expr_var) {
      char *base_name = base_result.value.expr->expr->var.name;
      size_t len = strlen(base_name) + strlen(e->attr.id) + 2; // +2 for '.' and '\0'
      char *new_name = region_alloc(region, len);
      snprintf(new_name, len, "%s.%s", base_name, e->attr.id);
      result = mkNKI_Expr_var(new_name, region);
    } else {
      result = mkNKI_Expr_proj(base_result.value.expr, e->attr.id, region);
    }
    break;
  }

  case Python_Expr_tuple:
  case Python_Expr_list: {
    struct Python_Expr_List *list =
        (e->tag == Python_Expr_tuple) ? e->tuple.xs : e->list.xs;
    struct SimplifyResult exprs_result = exprs_convert(list, region);
    if (!exprs_result.success) {
      return exprs_result;
    }
    result = mkNKI_Expr_tuple(exprs_result.value.expr_list, region);
    break;
  }

  case Python_Expr_subscript: {
    struct SimplifyResult base_result =
        expr_convert(e->subscript.tensor, region);
    if (!base_result.success) {
      return base_result;
    }

    struct SimplifyResult indices_result =
        indexes_convert(e->subscript.index, region);
    if (!indices_result.success) {
      return indices_result;
    }

    result = mkNKI_Expr_access(base_result.value.expr,
                               indices_result.value.index_list, region);
    break;
  }

  case Python_Expr_slice: {
    return make_error("invalid use of slice", NULL);
  }

  case Python_Expr_boolOp: {
    struct SimplifyResult exprs_result =
        exprs_convert(e->boolOp.values, region);
    if (!exprs_result.success) {
      return exprs_result;
    }

    enum NKI_BinOp op = boolOp_convert(e->boolOp.op);
    struct SimplifyResult bool_result =
        booleanOp_convert(op, exprs_result.value.expr_list, region);
    if (!bool_result.success) {
      return bool_result;
    }

    return bool_result; // Return the expression directly
  }

  case Python_Expr_binOp: {
    struct SimplifyResult op_result = binOp_convert(e->binOp.op);
    if (!op_result.success) {
      return op_result;
    }

    struct SimplifyResult left_result = expr_convert(e->binOp.left, region);
    if (!left_result.success) {
      return left_result;
    }

    struct SimplifyResult right_result = expr_convert(e->binOp.right, region);
    if (!right_result.success) {
      return right_result;
    }

    result = mkNKI_Expr_binOp(op_result.value.binop, left_result.value.expr,
                              right_result.value.expr, region);
    break;
  }

  case Python_Expr_unaryOp: {
    struct SimplifyResult operand_result =
        expr_convert(e->unaryOp.operand, region);
    if (!operand_result.success) {
      return operand_result;
    }

    return unaryOp_convert(e->unaryOp.op, operand_result.value.expr, region);
  }

  case Python_Expr_compare: {
    struct SimplifyResult left_result = expr_convert(e->compare.left, region);
    if (!left_result.success) {
      return left_result;
    }

    struct SimplifyResult comparators_result =
        exprs_convert(e->compare.comparators, region);
    if (!comparators_result.success) {
      return comparators_result;
    }

    return compare_convert(left_result.value.expr, e->compare.ops,
                           comparators_result.value.expr_list, region);
  }

  case Python_Expr_ifExp: {
    struct SimplifyResult test_result = expr_convert(e->ifExp.test, region);
    if (!test_result.success) {
      return test_result;
    }

    struct SimplifyResult body_result = expr_convert(e->ifExp.body, region);
    if (!body_result.success) {
      return body_result;
    }

    struct SimplifyResult orelse_result = expr_convert(e->ifExp.orelse, region);
    if (!orelse_result.success) {
      return orelse_result;
    }

    result = mkNKI_Expr_ifExp(test_result.value.expr, body_result.value.expr,
                              orelse_result.value.expr, region);
    break;
  }

  case Python_Expr_call: {
    struct SimplifyResult func_result = expr_convert(e->call.f, region);
    if (!func_result.success) {
      return func_result;
    }

    struct SimplifyResult args_result = exprs_convert(e->call.args, region);
    if (!args_result.success) {
      return args_result;
    }

    struct SimplifyResult kws_result =
        keywords_convert(e->call.keywords, region);
    if (!kws_result.success) {
      return kws_result;
    }

    result =
        mkNKI_Expr_call(func_result.value.expr, args_result.value.expr_list,
                        kws_result.value.keyword_list, region);
    break;
  }

  default:
    return make_error("unknown expression type", NULL);
  }

  return make_success_expr(result);
}

// Convert Python expression to NKI index list
static struct SimplifyResult indexes_convert(struct Python_Expr *e,
                                             struct region *region) {
  if (!e || !e->expr || !e->pos) {
    return make_error("invalid index expression", NULL);
  }

  struct NKI_Index_List *result_list;
  struct NKI_Index *index;

  switch (e->expr->tag) {
  case Python_Expr_slice: {
    // Handle slice: [l:u:step]
    index = region_alloc(region, sizeof(*index));
    index->tag = NKI_Index_slice;

    // Convert lower bound (optional)
    if (e->expr->slice.l) {
      struct SimplifyResult l_result = expr_convert(e->expr->slice.l, region);
      if (!l_result.success) {
        return l_result;
      }
      index->slice.l = l_result.value.expr;
    } else {
      index->slice.l = NULL;
    }

    // Convert upper bound (optional)
    if (e->expr->slice.u) {
      struct SimplifyResult u_result = expr_convert(e->expr->slice.u, region);
      if (!u_result.success) {
        return u_result;
      }
      index->slice.u = u_result.value.expr;
    } else {
      index->slice.u = NULL;
    }

    // Convert step (optional)
    if (e->expr->slice.step) {
      struct SimplifyResult step_result =
          expr_convert(e->expr->slice.step, region);
      if (!step_result.success) {
        return step_result;
      }
      index->slice.step = step_result.value.expr;
    } else {
      index->slice.step = NULL;
    }

    result_list = region_alloc(region, sizeof(*result_list));
    result_list->index = index;
    result_list->next = NULL;
    break;
  }

  case Python_Expr_tuple:
  case Python_Expr_list: {
    // Handle multiple coordinates: [i, j, k]
    struct Python_Expr_List *exprs = (e->expr->tag == Python_Expr_tuple)
                                         ? e->expr->tuple.xs
                                         : e->expr->list.xs;

    // Convert each expression to a coordinate index
    struct NKI_Index_List *index_list = NULL;
    struct NKI_Index_List **tail = &index_list;

    while (exprs) {
      struct SimplifyResult expr_result = indexes_convert(exprs->expr, region);
      if (!expr_result.success) {
        return expr_result;
      }

      *tail = expr_result.value.index_list;
      while (*tail)
        tail = &(*tail)->next;

      exprs = exprs->next;
    }

    result_list = index_list;
    break;
  }

  default: {
    // Single coordinate
    struct SimplifyResult expr_result = expr_prime_convert(e->expr, region);
    if (!expr_result.success) {
      return expr_result;
    }

    // Create NKI_Expr with position
    struct NKI_Expr *coord_expr = region_alloc(region, sizeof(*coord_expr));
    coord_expr->expr = expr_result.value.expr->expr;
    coord_expr->pos = e->pos;

    index = region_alloc(region, sizeof(*index));
    index->tag = NKI_Index_coord;
    index->coord.i = coord_expr;

    result_list = region_alloc(region, sizeof(*result_list));
    result_list->index = index;
    result_list->next = NULL;
    break;
  }
  }

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.index_list = result_list;
  return final_result;
}

// Convert Python keywords to NKI keywords
static struct SimplifyResult keywords_convert(struct Python_Keyword_List *ks,
                                              struct region *region) {
  if (!ks) {
    struct SimplifyResult result = {0};
    result.success = true;
    result.value.keyword_list = NULL;
    return result;
  }

  struct SimplifyResult expr_result = expr_convert(ks->keyword->value, region);
  if (!expr_result.success) {
    return expr_result;
  }

  struct SimplifyResult rest_result = keywords_convert(ks->next, region);
  if (!rest_result.success) {
    return rest_result;
  }

  struct NKI_Keyword *keyword = region_alloc(region, sizeof(*keyword));
  keyword->name = ks->keyword->id;
  keyword->expr = expr_result.value.expr;

  struct NKI_Keyword_List *result = region_alloc(region, sizeof(*result));
  result->keyword = keyword;
  result->next = rest_result.value.keyword_list;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.keyword_list = result;
  return final_result;
}
// Forward declarations for statement conversion
static struct SimplifyResult stmt_convert(struct Python_Stmt *s,
                                          struct region *region);
static struct SimplifyResult stmts_convert(struct Python_Stmt_List *s,
                                           struct region *region);
static struct SimplifyResult stmt_prime_convert(struct Python_Stmt_ *s,
                                                struct region *region);

// Convert Python variable expression to NKI variable expression
static struct SimplifyResult var_convert(struct Python_Expr *x,
                                         struct region *region) {
  struct SimplifyResult expr_result = expr_convert(x, region);
  if (!expr_result.success) {
    return expr_result;
  }

  // TODO we may want this restriction in future
  //if (expr_result.value.expr->expr->tag != NKI_Expr_var) {
  //  return make_error("cannot assign to expression", NULL);
  //}

  return expr_result;
}

// Convert list of Python variable expressions to list of NKI variable
// expressions
static struct SimplifyResult vars_convert(struct Python_Expr_List *xs,
                                          struct region *region) {
  if (!xs) {
    struct SimplifyResult result = {0};
    result.success = true;
    result.value.expr_list = NULL;
    return result;
  }

  struct SimplifyResult var_result = var_convert(xs->expr, region);
  if (!var_result.success) {
    return var_result;
  }

  struct SimplifyResult rest_result = vars_convert(xs->next, region);
  if (!rest_result.success) {
    return rest_result;
  }

  struct NKI_Expr_List *result = region_alloc(region, sizeof(*result));
  result->expr = var_result.value.expr;
  result->next = rest_result.value.expr_list;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.expr_list = result;
  return final_result;
}

// Create assignment statements from variable list and expression
static struct SimplifyResult assign_convert(struct NKI_Expr_List *xs,
                                            struct NKI_Expr *e,
                                            struct region *region) {
  if (!xs) {
    return make_error("invalid assignment", NULL);
  }

  if (!xs->next) {
    // Single assignment: x = e
    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_assign;
    stmt_body->assign.x = xs->expr;
    stmt_body->assign.ty = NULL;
    stmt_body->assign.e = e;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;
    stmt->pos = xs->expr->pos; // Use position from variable

    struct NKI_Stmt_List *result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;

    struct SimplifyResult final_result = {0};
    final_result.success = true;
    final_result.value.stmts = result;
    return final_result;
  } else {
    // Multiple assignment: x, y, z = e
    // First assignment: x = e
    struct NKI_Stmt_ *first_stmt_body =
        region_alloc(region, sizeof(*first_stmt_body));
    first_stmt_body->tag = NKI_Stmt_assign;
    first_stmt_body->assign.x = xs->expr;
    first_stmt_body->assign.ty = NULL;
    first_stmt_body->assign.e = e;

    struct NKI_Stmt *first_stmt = region_alloc(region, sizeof(*first_stmt));
    first_stmt->stmt = first_stmt_body;
    first_stmt->pos = xs->expr->pos;

    // Rest assignments: y = x, z = x, ...
    struct NKI_Stmt_List *rest_stmts = NULL;
    struct NKI_Stmt_List **tail = &rest_stmts;

    struct NKI_Expr_List *rest_vars = xs->next;
    while (rest_vars) {
      struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
      stmt_body->tag = NKI_Stmt_assign;
      stmt_body->assign.x = rest_vars->expr;
      stmt_body->assign.ty = NULL;
      stmt_body->assign.e = xs->expr; // Assign from first variable

      struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
      stmt->stmt = stmt_body;
      stmt->pos = rest_vars->expr->pos;

      struct NKI_Stmt_List *node = region_alloc(region, sizeof(*node));
      node->stmt = stmt;
      node->next = NULL;

      *tail = node;
      tail = &node->next;
      rest_vars = rest_vars->next;
    }

    // Combine first statement with rest
    struct NKI_Stmt_List *result = region_alloc(region, sizeof(*result));
    result->stmt = first_stmt;
    result->next = rest_stmts;

    struct SimplifyResult final_result = {0};
    final_result.success = true;
    final_result.value.stmts = result;
    return final_result;
  }
}
// Convert Python statement to NKI statement list
static struct SimplifyResult stmt_convert(struct Python_Stmt *s,
                                          struct region *region) {
  if (!s || !s->stmt || !s->pos) {
    return make_error("invalid statement", NULL);
  }

  struct SimplifyResult stmt_result = stmt_prime_convert(s->stmt, region);
  if (!stmt_result.success) {
    return stmt_result;
  }

  // Add position to all statements in the list
  struct NKI_Stmt_List *stmt_list = stmt_result.value.stmts;
  while (stmt_list) {
    stmt_list->stmt->pos = s->pos;
    stmt_list = stmt_list->next;
  }

  return stmt_result;
}

// Convert list of Python statements to list of NKI statements
static struct SimplifyResult stmts_convert(struct Python_Stmt_List *s,
                                           struct region *region) {
  if (!s) {
    struct SimplifyResult result = {0};
    result.success = true;
    result.value.stmts = NULL;
    return result;
  }

  struct SimplifyResult stmt_result = stmt_convert(s->stmt, region);
  if (!stmt_result.success) {
    return stmt_result;
  }

  struct SimplifyResult rest_result = stmts_convert(s->next, region);
  if (!rest_result.success) {
    return rest_result;
  }

  // Flatten the statement lists
  struct NKI_Stmt_List *result = stmt_result.value.stmts;
  if (result) {
    // Find the end of the first list
    struct NKI_Stmt_List *tail = result;
    while (tail->next) {
      tail = tail->next;
    }
    // Append the rest
    tail->next = rest_result.value.stmts;
  } else {
    result = rest_result.value.stmts;
  }

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.stmts = result;
  return final_result;
}

// Convert Python statement body to NKI statement list
static struct SimplifyResult stmt_prime_convert(struct Python_Stmt_ *s,
                                                struct region *region) {
  if (!s) {
    return make_error("invalid statement", NULL);
  }

  struct NKI_Stmt_List *result = NULL;

  switch (s->tag) {
  case Python_Stmt_pass: {
    // Pass statement produces empty list
    struct SimplifyResult final_result = {0};
    final_result.success = true;
    final_result.value.stmts = NULL;
    return final_result;
  }

  case Python_Stmt_expr: {
    struct SimplifyResult expr_result = expr_convert(s->expr.e, region);
    if (!expr_result.success) {
      return expr_result;
    }

    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_expr;
    stmt_body->expr.e = expr_result.value.expr;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_assert: {
    struct SimplifyResult expr_result = expr_convert(s->assert.e, region);
    if (!expr_result.success) {
      return expr_result;
    }

    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_assert;
    stmt_body->assert.e = expr_result.value.expr;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_ret: {
    struct SimplifyResult expr_result = expr_convert(s->ret.e, region);
    if (!expr_result.success) {
      return expr_result;
    }

    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_ret;
    stmt_body->ret.e = expr_result.value.expr;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_assign: {
    struct SimplifyResult vars_result = vars_convert(s->assign.xs, region);
    if (!vars_result.success) {
      return vars_result;
    }

    struct SimplifyResult expr_result = expr_convert(s->assign.e, region);
    if (!expr_result.success) {
      return expr_result;
    }

    return assign_convert(vars_result.value.expr_list, expr_result.value.expr,
                          region);
  }

  case Python_Stmt_augAssign: {
    struct SimplifyResult var_result = var_convert(s->augAssign.x, region);
    if (!var_result.success) {
      return var_result;
    }

    struct SimplifyResult expr_result = expr_convert(s->augAssign.e, region);
    if (!expr_result.success) {
      return expr_result;
    }

    struct SimplifyResult op_result = binOp_convert(s->augAssign.op);
    if (!op_result.success) {
      return op_result;
    }

    // Create binary operation: x = x op e
    struct NKI_Expr *rhs =
        mkNKI_Expr_binOp(op_result.value.binop, var_result.value.expr,
                         expr_result.value.expr, region);

    struct NKI_Expr_List *var_list = region_alloc(region, sizeof(*var_list));
    var_list->expr = var_result.value.expr;
    var_list->next = NULL;

    return assign_convert(var_list, rhs, region);
  }

  case Python_Stmt_annAssign: {
    struct SimplifyResult var_result = var_convert(s->annAssign.x, region);
    if (!var_result.success) {
      return var_result;
    }

    struct SimplifyResult type_result =
        expr_convert(s->annAssign.annotation, region);
    if (!type_result.success) {
      return type_result;
    }

    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_assign;
    stmt_body->assign.x = var_result.value.expr;
    stmt_body->assign.ty = type_result.value.expr;

    if (s->annAssign.value) {
      struct SimplifyResult value_result =
          expr_convert(s->annAssign.value, region);
      if (!value_result.success) {
        return value_result;
      }
      stmt_body->assign.e = value_result.value.expr;
    } else {
      stmt_body->assign.e = NULL;
    }

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_ifStm: {
    struct SimplifyResult cond_result = expr_convert(s->ifStm.e, region);
    if (!cond_result.success) {
      return cond_result;
    }

    struct SimplifyResult then_result = stmts_convert(s->ifStm.thn, region);
    if (!then_result.success) {
      return then_result;
    }

    struct SimplifyResult else_result = stmts_convert(s->ifStm.els, region);
    if (!else_result.success) {
      return else_result;
    }

    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_ifStm;
    stmt_body->ifStm.e = cond_result.value.expr;
    stmt_body->ifStm.thn = then_result.value.stmts;
    stmt_body->ifStm.els = else_result.value.stmts;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_forLoop: {
    if (s->forLoop.orelse && s->forLoop.orelse->stmt) {
      return make_error("for else is not supported in NKI", NULL);
    }

    struct SimplifyResult var_result = expr_convert(s->forLoop.x, region);
    if (!var_result.success) {
      return var_result;
    }

    struct SimplifyResult iter_result = expr_convert(s->forLoop.iter, region);
    if (!iter_result.success) {
      return iter_result;
    }

    struct SimplifyResult body_result = stmts_convert(s->forLoop.body, region);
    if (!body_result.success) {
      return body_result;
    }

    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_forLoop;
    stmt_body->forLoop.x = var_result.value.expr;
    stmt_body->forLoop.iter = iter_result.value.expr;
    stmt_body->forLoop.body = body_result.value.stmts;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_breakLoop: {
    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_breakLoop;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  case Python_Stmt_continueLoop: {
    struct NKI_Stmt_ *stmt_body = region_alloc(region, sizeof(*stmt_body));
    stmt_body->tag = NKI_Stmt_continueLoop;

    struct NKI_Stmt *stmt = region_alloc(region, sizeof(*stmt));
    stmt->stmt = stmt_body;

    result = region_alloc(region, sizeof(*result));
    result->stmt = stmt;
    result->next = NULL;
    break;
  }

  default:
    return make_error("unknown statement type", NULL);
  }

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.stmts = result;
  return final_result;
}
// Convert Python function parameters to NKI parameters
static struct SimplifyResult params_convert(struct Python_Args *args,
                                            struct region *region) {
  if (args->vararg) {
    return make_error("varargs are not supported in NKI", NULL);
  }

  if (args->kwarg) {
    // Warning: variable keyword arguments are not supported in NKI
    // But we continue processing
  }

  if (args->posonlyargs && args->posonlyargs->s) {
    // Warning: position-only arguments are not supported in NKI
  }

  if (args->kwonlyargs && args->kwonlyargs->s) {
    // Warning: keyword-only arguments are not supported in NKI
  }

  // Process regular arguments with defaults
  struct NKI_Param_List *result = NULL;
  struct NKI_Param_List **tail = &result;

  // Combine args and defaults
  struct String_List *arg_names = args->args;
  struct Python_Keyword_List *defaults = args->kw_defaults;

  while (arg_names) {
    struct NKI_Param *param = region_alloc(region, sizeof(*param));
    param->name = arg_names->s;
    param->dflt = NULL;

    // Look for default value
    struct Python_Keyword_List *default_iter = defaults;
    while (default_iter) {
      if (default_iter->keyword && default_iter->keyword->id &&
          strcmp(default_iter->keyword->id, arg_names->s) == 0) {
        struct SimplifyResult default_result =
            expr_convert(default_iter->keyword->value, region);
        if (!default_result.success) {
          return default_result;
        }
        param->dflt = default_result.value.expr;
        break;
      }
      default_iter = default_iter->next;
    }

    struct NKI_Param_List *node = region_alloc(region, sizeof(*node));
    node->param = param;
    node->next = NULL;

    *tail = node;
    tail = &node->next;

    arg_names = arg_names->next;
  }

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.param_list = result;
  return final_result;
}

// Convert Python function to NKI function
static struct SimplifyResult func_convert(struct Python_Fun *f,
                                          struct region *region) {
  struct SimplifyResult params_result = params_convert(f->args, region);
  if (!params_result.success) {
    return params_result;
  }

  struct SimplifyResult body_result = stmts_convert(f->body, region);
  if (!body_result.success) {
    return body_result;
  }

  struct NKI_Fun *result = region_alloc(region, sizeof(*result));
  result->name = f->name;
  result->file = "unknown"; // TODO: fix me
  result->line = f->line;
  result->args = params_result.value.param_list;
  result->body = body_result.value.stmts;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.fun = result;
  return final_result;
}

// Convert Python keywords to NKI arguments
static struct SimplifyResult kwargs_convert(struct Python_Keyword_List *kws,
                                            struct region *region) {
  if (!kws) {
    struct SimplifyResult result = {0};
    result.success = true;
    result.value.arg_list = NULL;
    return result;
  }

  struct SimplifyResult expr_result = expr_convert(kws->keyword->value, region);
  if (!expr_result.success) {
    return expr_result;
  }

  struct SimplifyResult rest_result = kwargs_convert(kws->next, region);
  if (!rest_result.success) {
    return rest_result;
  }

  struct NKI_Arg *arg = region_alloc(region, sizeof(*arg));
  arg->name = kws->keyword->id;
  arg->value = expr_result.value.expr;

  struct NKI_Arg_List *result = region_alloc(region, sizeof(*result));
  result->arg = arg;
  result->next = rest_result.value.arg_list;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.arg_list = result;
  return final_result;
}

// Convert function arguments (positional and keyword)
static struct SimplifyResult args_convert(struct NKI_Param_List *params,
                                          struct Python_Expr_List *args,
                                          struct Python_Keyword_List *kws,
                                          struct region *region) {
  struct NKI_Arg_List *result = NULL;
  struct NKI_Arg_List **tail = &result;

  // Handle positional arguments first
  struct NKI_Param_List *param_iter = params;
  struct Python_Expr_List *arg_iter = args;

  while (param_iter && arg_iter) {
    struct SimplifyResult expr_result = expr_convert(arg_iter->expr, region);
    if (!expr_result.success) {
      return expr_result;
    }

    struct NKI_Arg *arg = region_alloc(region, sizeof(*arg));
    arg->name = param_iter->param->name;
    arg->value = expr_result.value.expr;

    struct NKI_Arg_List *node = region_alloc(region, sizeof(*node));
    node->arg = arg;
    node->next = NULL;

    *tail = node;
    tail = &node->next;

    param_iter = param_iter->next;
    arg_iter = arg_iter->next;
  }

  // Handle remaining parameters with keyword arguments
  while (param_iter) {
    struct Python_Keyword_List *kw_iter = kws;
    bool found = false;

    while (kw_iter) {
      if (kw_iter->keyword && kw_iter->keyword->id &&
          strcmp(kw_iter->keyword->id, param_iter->param->name) == 0) {
        struct SimplifyResult expr_result =
            expr_convert(kw_iter->keyword->value, region);
        if (!expr_result.success) {
          return expr_result;
        }

        struct NKI_Arg *arg = region_alloc(region, sizeof(*arg));
        arg->name = param_iter->param->name;
        arg->value = expr_result.value.expr;

        struct NKI_Arg_List *node = region_alloc(region, sizeof(*node));
        node->arg = arg;
        node->next = NULL;

        *tail = node;
        tail = &node->next;

        found = true;
        break;
      }
      kw_iter = kw_iter->next;
    }

    if (!found) {
      char error_msg[256];
      snprintf(error_msg, sizeof(error_msg), "argument %s not supplied",
               param_iter->param->name);
      return make_error(region_strdup(region, error_msg), NULL);
    }

    param_iter = param_iter->next;
  }

  // Reverse the result list to maintain order
  struct NKI_Arg_List *reversed = NULL;
  while (result) {
    struct NKI_Arg_List *next = result->next;
    result->next = reversed;
    reversed = result;
    result = next;
  }

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.arg_list = reversed;
  return final_result;
}

// Convert Python kernel to NKI kernel
static struct SimplifyResult kernel_convert(struct Python_Kernel *py,
                                            struct region *region) {
  // Convert all functions
  struct NKI_Fun_List *funs = NULL;
  struct NKI_Fun_List **funs_tail = &funs;

  struct Python_Fun_List *py_fun_iter = py->funcs;
  while (py_fun_iter) {
    struct SimplifyResult fun_result = func_convert(py_fun_iter->fun, region);
    if (!fun_result.success) {
      return fun_result;
    }

    struct NKI_Fun_List *node = region_alloc(region, sizeof(*node));
    node->fun = fun_result.value.fun;
    node->next = NULL;

    *funs_tail = node;
    funs_tail = &node->next;

    py_fun_iter = py_fun_iter->next;
  }

  // Find main function
  struct NKI_Fun *main_fun = NULL;
  struct NKI_Fun_List *fun_iter = funs;
  while (fun_iter) {
    if (strcmp(fun_iter->fun->name, py->entry) == 0) {
      main_fun = fun_iter->fun;
      break;
    }
    fun_iter = fun_iter->next;
  }

  if (!main_fun) {
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg), "entry function %s not found",
             py->entry);
    return make_error(region_strdup(region, error_msg), NULL);
  }

  // Convert arguments
  struct SimplifyResult args_result =
      args_convert(main_fun->args, py->args, py->kwargs, region);
  if (!args_result.success) {
    return args_result;
  }

  // Convert globals
  struct SimplifyResult globals_result = kwargs_convert(py->globals, region);
  if (!globals_result.success) {
    return globals_result;
  }

  struct NKI_Kernel *result = region_alloc(region, sizeof(*result));
  result->entry = py->entry;
  result->funs = funs;
  result->args = args_result.value.arg_list;
  result->globals = globals_result.value.arg_list;

  struct SimplifyResult final_result = {0};
  final_result.success = true;
  final_result.value.kernel = result;
  return final_result;
}

// Main simplification function
struct SimpResult simplify(struct Python_Kernel *py) {
  struct SimpResult res = {0};

  if (!py) {
    res.ok = false;
    res.err = "Python kernel is NULL";
    return res;
  }

  struct region *region = region_create();
  if (!region) {
    res.ok = false;
    res.err = "Unable to create memory region";
    return res;
  }
  res.region = region;

  struct SimplifyResult result = kernel_convert(py, region);

  if (result.success) {
    res.ok = true;
    res.err = NULL;
    res.kernel = result.value.kernel;
  } else {
    res.ok = false;
    res.err = result.error.message;
    res.kernel = NULL;
  }
  return res;
}
