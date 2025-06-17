/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin, Claude
*/

// This code was entirely written by Q

#include "stdc.h"
#include "region.c"
#include "simplify.c"
#include <assert.h>

// Test counter
static int tests_run = 0;
static int tests_passed = 0;

#define TEST(name)                                                             \
  do {                                                                         \
    printf("Running test: %s\n", #name);                                       \
    tests_run++;                                                               \
    if (test_##name()) {                                                       \
      printf("  PASSED\n");                                                    \
      tests_passed++;                                                          \
    } else {                                                                   \
      printf("  FAILED\n");                                                    \
    }                                                                          \
  } while (0)

// Helper function to create a test region
static struct region *create_test_region() { return region_create(); }

// Helper function to test simplify with the new interface
static bool test_simplify_success(struct Python_Kernel *py_kernel) {
  struct SimpResult result = simplify(py_kernel);
  bool success = result.ok && result.kernel != NULL;
  
  if (!success && result.err) {
    printf("    Error: %s\n", result.err);
  }
  
  // Clean up the result region if it was created
  if (result.region) {
    region_destroy(result.region);
  }
  
  return success;
}

// Helper function to test simplify expecting failure
static bool test_simplify_failure(struct Python_Kernel *py_kernel, const char *expected_error) {
  struct SimpResult result = simplify(py_kernel);
  bool success = !result.ok && result.err != NULL;
  
  if (expected_error && success) {
    success = strstr(result.err, expected_error) != NULL;
  }
  
  if (!success) {
    printf("    Expected error containing '%s', got: %s\n",
           expected_error ? expected_error : "any error",
           result.err ? result.err : "no error");
  }
  
  // Clean up the result region if it was created
  if (result.region) {
    region_destroy(result.region);
  }
  
  return success;
}

// Helper function to create a position structure
static struct Python_Pos *make_python_pos(struct region *region) {
  struct Python_Pos *pos = region_alloc(region, sizeof(*pos));
  if (!pos)
    return NULL;

  pos->lineno = 1;
  pos->col_offset = 0;
  pos->end_lineno = 1;
  pos->end_col_offset = 0;

  return pos;
}

// Helper function to create a Python constant expression (manual construction)
static struct Python_Expr *make_python_const_int(int value,
                                                 struct region *region) {
  // Allocate the constant value
  struct Python_Const *const_val = region_alloc(region, sizeof(*const_val));
  if (!const_val)
    return NULL;

  const_val->tag = Python_Const_int;
  const_val->i.value = value;

  // Allocate the expression
  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  // Allocate the inner expression structure
  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  // Set up the expression
  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_const;
  expr->expr->c.value = const_val;

  return expr;
}

// Helper function to create a Python variable expression (manual construction)
static struct Python_Expr *make_python_var(const char *name,
                                           struct region *region) {
  // Allocate the expression
  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  // Allocate the inner expression structure
  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  // Set up the expression
  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_name;
  expr->expr->name.id = (char *)name;
  expr->expr->name.ctx = Python_Ctx_load;

  return expr;
}

// Helper function to create a Python binary operation (manual construction)
static struct Python_Expr *make_python_binop(enum Python_BinOp op,
                                             struct Python_Expr *left,
                                             struct Python_Expr *right,
                                             struct region *region) {
  // Allocate the expression
  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  // Allocate the inner expression structure
  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  // Set up the expression
  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_binOp;
  expr->expr->binOp.op = op;
  expr->expr->binOp.left = left;
  expr->expr->binOp.right = right;

  return expr;
}

// Helper function to create a return statement (manual construction)
static struct Python_Stmt *make_return_stmt(struct Python_Expr *value,
                                            struct region *region) {
  // Allocate the statement
  struct Python_Stmt *stmt = region_alloc(region, sizeof(*stmt));
  if (!stmt)
    return NULL;

  // Allocate the inner statement structure
  stmt->stmt = region_alloc(region, sizeof(*stmt->stmt));
  if (!stmt->stmt)
    return NULL;

  // Set up the statement
  stmt->pos = make_python_pos(region);
  if (!stmt->pos)
    return NULL;

  stmt->stmt->tag = Python_Stmt_ret;
  stmt->stmt->ret.e = value;

  return stmt;
}

// Helper function to create an assignment statement (manual construction)
static struct Python_Stmt *make_assignment(const char *var_name,
                                           struct Python_Expr *value,
                                           struct region *region) {
  // Create target variable
  struct Python_Expr *target = make_python_var(var_name, region);
  if (!target)
    return NULL;

  // Create target list
  struct Python_Expr_List *targets = region_alloc(region, sizeof(*targets));
  if (!targets)
    return NULL;

  targets->expr = target;
  targets->next = NULL;

  // Allocate the statement
  struct Python_Stmt *stmt = region_alloc(region, sizeof(*stmt));
  if (!stmt)
    return NULL;

  // Allocate the inner statement structure
  stmt->stmt = region_alloc(region, sizeof(*stmt->stmt));
  if (!stmt->stmt)
    return NULL;

  // Set up the statement
  stmt->pos = make_python_pos(region);
  if (!stmt->pos)
    return NULL;

  stmt->stmt->tag = Python_Stmt_assign;
  stmt->stmt->assign.xs = targets;
  stmt->stmt->assign.e = value;

  return stmt;
}

// Helper function to create a pass statement (manual construction)
static struct Python_Stmt *make_pass_stmt(struct region *region) {
  // Allocate the statement
  struct Python_Stmt *stmt = region_alloc(region, sizeof(*stmt));
  if (!stmt)
    return NULL;

  // Allocate the inner statement structure
  stmt->stmt = region_alloc(region, sizeof(*stmt->stmt));
  if (!stmt->stmt)
    return NULL;

  // Set up the statement
  stmt->pos = make_python_pos(region);
  if (!stmt->pos)
    return NULL;

  stmt->stmt->tag = Python_Stmt_pass;

  return stmt;
}

// Helper function to create a minimal kernel for testing
static struct Python_Kernel *make_test_kernel(const char *entry_name,
                                              struct Python_Stmt_List *body,
                                              struct region *region) {
  // Create function arguments (empty)
  struct Python_Args *args = region_alloc(region, sizeof(*args));
  if (!args)
    return NULL;

  args->args = NULL;
  args->posonlyargs = NULL;
  args->kwonlyargs = NULL;
  args->kw_defaults = NULL;
  args->defaults = NULL;
  args->vararg = NULL;
  args->kwarg = NULL;

  // Create function
  struct Python_Fun *fun = region_alloc(region, sizeof(*fun));
  if (!fun)
    return NULL;

  fun->name = (char *)entry_name;
  fun->line = 1;
  fun->source = "test.py";
  fun->args = args;
  fun->body = body;

  // Create function list
  struct Python_Fun_List *funs = region_alloc(region, sizeof(*funs));
  if (!funs)
    return NULL;
  funs->fun = fun;
  funs->next = NULL;

  // Create kernel
  struct Python_Kernel *kernel = region_alloc(region, sizeof(*kernel));
  if (!kernel)
    return NULL;

  kernel->entry = (char *)entry_name;
  kernel->funcs = funs;
  kernel->args = NULL;
  kernel->kwargs = NULL;
  kernel->globals = NULL;
  kernel->undefinedSymbols = NULL;

  return kernel;
}

// Test 1: Basic constant conversion
static bool test_constant_conversion() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create a simple function that returns 42
  struct Python_Expr *const_expr = make_python_const_int(42, region);
  if (!const_expr) {
    region_destroy(region);
    return false;
  }

  // Create return statement
  struct Python_Stmt *return_stmt = make_return_stmt(const_expr, region);
  if (!return_stmt) {
    region_destroy(region);
    return false;
  }

  // Create statement list
  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = return_stmt;
  body->next = NULL;

  // Create kernel
  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Test simplify
  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 2: Binary operation conversion
static bool test_binary_operations() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test addition: x = 1 + 2
  struct Python_Expr *left = make_python_const_int(1, region);
  struct Python_Expr *right = make_python_const_int(2, region);
  struct Python_Expr *add_expr =
      make_python_binop(Python_BinOp_add, left, right, region);

  if (!left || !right || !add_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("x", add_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  // Create statement list
  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  // Create kernel
  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Test simplify
  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 3: Unsupported operator error handling
static bool test_unsupported_operators() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test matrix multiplication (should fail)
  struct Python_Expr *left = make_python_var("a", region);
  struct Python_Expr *right = make_python_var("b", region);
  struct Python_Expr *matmul_expr =
      make_python_binop(Python_BinOp_matmul, left, right, region);

  if (!left || !right || !matmul_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("x", matmul_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  // Create statement list
  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  // Create kernel
  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Test simplify - should fail
  bool success = test_simplify_failure(py_kernel, "matmul");

  region_destroy(region);
  return success;
}

// Test 4: Entry function not found error
static bool test_entry_function_not_found() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create empty body
  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = make_pass_stmt(region);
  body->next = NULL;

  // Create kernel with wrong entry name
  struct Python_Kernel *py_kernel =
      make_test_kernel("wrong_name", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Change entry to look for different function
  py_kernel->entry = "main";

  // Test simplify - should fail
  bool success = test_simplify_failure(py_kernel, "entry function");

  region_destroy(region);
  return success;
}

// Test 5: Variable handling
static bool test_variable_handling() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test simple variable assignment: y = x
  struct Python_Expr *var_expr = make_python_var("x", region);
  if (!var_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("y", var_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  // Create statement list
  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  // Create kernel
  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Test simplify
  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 6: Multiple supported binary operators
static bool test_supported_binary_operators() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test each supported binary operator
  enum Python_BinOp ops[] = {
      Python_BinOp_add,    Python_BinOp_sub,    Python_BinOp_mul,
      Python_BinOp_div,    Python_BinOp_mod,    Python_BinOp_pow,
      Python_BinOp_lshift, Python_BinOp_rshift, Python_BinOp_or,
      Python_BinOp_xor,    Python_BinOp_and,    Python_BinOp_floor};

  int num_ops = sizeof(ops) / sizeof(ops[0]);
  bool all_success = true;

  for (int i = 0; i < num_ops; i++) {
    struct Python_Expr *left = make_python_const_int(5, region);
    struct Python_Expr *right = make_python_const_int(3, region);
    struct Python_Expr *binop_expr =
        make_python_binop(ops[i], left, right, region);

    if (!left || !right || !binop_expr) {
      printf("    Failed to create expressions for operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt *assign_stmt =
        make_assignment("result", binop_expr, region);
    if (!assign_stmt) {
      printf("    Failed to create assignment for operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    // Create statement list
    struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
    if (!body) {
      printf("    Failed to create body for operator %d\n", ops[i]);
      all_success = false;
      break;
    }
    body->stmt = assign_stmt;
    body->next = NULL;

    // Create kernel
    struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
    if (!py_kernel) {
      printf("    Failed to create kernel for operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    // Test this operator
    if (!test_simplify_success(py_kernel)) {
      printf("    Failed on operator %d\n", ops[i]);
      all_success = false;
      break;
    }
  }

  region_destroy(region);
  return all_success;
}

// Test 7: Multiple statements
static bool test_multiple_statements() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create two statements: x = 1; y = 2
  struct Python_Expr *const1 = make_python_const_int(1, region);
  struct Python_Expr *const2 = make_python_const_int(2, region);

  if (!const1 || !const2) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *stmt1 = make_assignment("x", const1, region);
  struct Python_Stmt *stmt2 = make_assignment("y", const2, region);

  if (!stmt1 || !stmt2) {
    region_destroy(region);
    return false;
  }

  // Create statement list
  struct Python_Stmt_List *body2 = region_alloc(region, sizeof(*body2));
  struct Python_Stmt_List *body1 = region_alloc(region, sizeof(*body1));
  if (!body1 || !body2) {
    region_destroy(region);
    return false;
  }

  body1->stmt = stmt1;
  body1->next = body2;
  body2->stmt = stmt2;
  body2->next = NULL;

  // Create kernel
  struct Python_Kernel *py_kernel = make_test_kernel("main", body1, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Test simplify
  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 8: Different constant types
static bool test_different_constants() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test boolean constant
  struct Python_Const *bool_val = region_alloc(region, sizeof(*bool_val));
  if (!bool_val) {
    region_destroy(region);
    return false;
  }
  bool_val->tag = Python_Const_bool;
  bool_val->b.value = true;

  struct Python_Expr *bool_expr = region_alloc(region, sizeof(*bool_expr));
  if (!bool_expr) {
    region_destroy(region);
    return false;
  }
  bool_expr->expr = region_alloc(region, sizeof(*bool_expr->expr));
  if (!bool_expr->expr) {
    region_destroy(region);
    return false;
  }
  bool_expr->pos = make_python_pos(region);
  if (!bool_expr->pos) {
    region_destroy(region);
    return false;
  }
  bool_expr->expr->tag = Python_Expr_const;
  bool_expr->expr->c.value = bool_val;

  struct Python_Stmt *assign_stmt = make_assignment("flag", bool_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  // Create statement list
  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  // Create kernel
  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  // Test simplify
  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Helper function to create a Python string constant
static struct Python_Expr *make_python_const_string(const char *value,
                                                    struct region *region) {
  struct Python_Const *const_val = region_alloc(region, sizeof(*const_val));
  if (!const_val)
    return NULL;

  const_val->tag = Python_Const_string;
  const_val->s.value = (char *)value;

  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_const;
  expr->expr->c.value = const_val;

  return expr;
}

// Helper function to create a Python float constant
static struct Python_Expr *make_python_const_float(double value,
                                                   struct region *region) {
  struct Python_Const *const_val = region_alloc(region, sizeof(*const_val));
  if (!const_val)
    return NULL;

  const_val->tag = Python_Const_float;
  const_val->f.value = value;

  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_const;
  expr->expr->c.value = const_val;

  return expr;
}

// Helper function to create a Python unary operation
static struct Python_Expr *make_python_unaryop(enum Python_UnaryOp op,
                                               struct Python_Expr *operand,
                                               struct region *region) {
  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_unaryOp;
  expr->expr->unaryOp.op = op;
  expr->expr->unaryOp.operand = operand;

  return expr;
}

// Helper function to create a Python comparison operation
static struct Python_Expr *make_python_compare(struct Python_Expr *left,
                                               enum Python_CmpOp op,
                                               struct Python_Expr *right,
                                               struct region *region) {
  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  // Create operator list
  struct Python_CmpOp_List *ops = region_alloc(region, sizeof(*ops));
  if (!ops)
    return NULL;
  ops->cmpop = op;
  ops->next = NULL;

  // Create comparator list
  struct Python_Expr_List *comparators = region_alloc(region, sizeof(*comparators));
  if (!comparators)
    return NULL;
  comparators->expr = right;
  comparators->next = NULL;

  expr->expr->tag = Python_Expr_compare;
  expr->expr->compare.left = left;
  expr->expr->compare.ops = ops;
  expr->expr->compare.comparators = comparators;

  return expr;
}

// Test 9: NULL input handling
static bool test_null_input_handling() {
  // Test with NULL kernel
  bool success = test_simplify_failure(NULL, "NULL");
  return success;
}

// Test 10: String constants
static bool test_string_constants() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  struct Python_Expr *str_expr = make_python_const_string("hello", region);
  if (!str_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("message", str_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 11: Float constants
static bool test_float_constants() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  struct Python_Expr *float_expr = make_python_const_float(3.14, region);
  if (!float_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("pi", float_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 12: Unary operators
static bool test_unary_operators() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test all supported unary operators
  enum Python_UnaryOp ops[] = {
      Python_UnaryOp_invert,
      Python_UnaryOp_not,
      Python_UnaryOp_uadd,
      Python_UnaryOp_usub
  };

  int num_ops = sizeof(ops) / sizeof(ops[0]);
  bool all_success = true;

  for (int i = 0; i < num_ops; i++) {
    struct Python_Expr *operand = make_python_const_int(5, region);
    struct Python_Expr *unary_expr = make_python_unaryop(ops[i], operand, region);

    if (!operand || !unary_expr) {
      printf("    Failed to create expressions for unary operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt *assign_stmt = make_assignment("result", unary_expr, region);
    if (!assign_stmt) {
      printf("    Failed to create assignment for unary operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
    if (!body) {
      printf("    Failed to create body for unary operator %d\n", ops[i]);
      all_success = false;
      break;
    }
    body->stmt = assign_stmt;
    body->next = NULL;

    struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
    if (!py_kernel) {
      printf("    Failed to create kernel for unary operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    if (!test_simplify_success(py_kernel)) {
      printf("    Failed on unary operator %d\n", ops[i]);
      all_success = false;
      break;
    }
  }

  region_destroy(region);
  return all_success;
}

// Test 13: Comparison operators
static bool test_comparison_operators() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test supported comparison operators
  enum Python_CmpOp ops[] = {
      Python_CmpOp_eq,
      Python_CmpOp_ne,
      Python_CmpOp_lt,
      Python_CmpOp_le,
      Python_CmpOp_gt,
      Python_CmpOp_ge
  };

  int num_ops = sizeof(ops) / sizeof(ops[0]);
  bool all_success = true;

  for (int i = 0; i < num_ops; i++) {
    struct Python_Expr *left = make_python_const_int(5, region);
    struct Python_Expr *right = make_python_const_int(3, region);
    struct Python_Expr *cmp_expr = make_python_compare(left, ops[i], right, region);

    if (!left || !right || !cmp_expr) {
      printf("    Failed to create expressions for comparison operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt *assign_stmt = make_assignment("result", cmp_expr, region);
    if (!assign_stmt) {
      printf("    Failed to create assignment for comparison operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
    if (!body) {
      printf("    Failed to create body for comparison operator %d\n", ops[i]);
      all_success = false;
      break;
    }
    body->stmt = assign_stmt;
    body->next = NULL;

    struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
    if (!py_kernel) {
      printf("    Failed to create kernel for comparison operator %d\n", ops[i]);
      all_success = false;
      break;
    }

    if (!test_simplify_success(py_kernel)) {
      printf("    Failed on comparison operator %d\n", ops[i]);
      all_success = false;
      break;
    }
  }

  region_destroy(region);
  return all_success;
}

// Test 14: Unsupported comparison operators
static bool test_unsupported_comparison_operators() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test unsupported comparison operators
  enum Python_CmpOp unsupported_ops[] = {
      Python_CmpOp_is,
      Python_CmpOp_isNot,
      Python_CmpOp_isIn,
      Python_CmpOp_notIn
  };

  const char *expected_errors[] = {
      "is operator",
      "is operator", 
      "in operator",
      "in operator"
  };

  int num_ops = sizeof(unsupported_ops) / sizeof(unsupported_ops[0]);
  bool all_success = true;

  for (int i = 0; i < num_ops; i++) {
    struct Python_Expr *left = make_python_var("a", region);
    struct Python_Expr *right = make_python_var("b", region);
    struct Python_Expr *cmp_expr = make_python_compare(left, unsupported_ops[i], right, region);

    if (!left || !right || !cmp_expr) {
      printf("    Failed to create expressions for unsupported comparison operator %d\n", unsupported_ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt *assign_stmt = make_assignment("result", cmp_expr, region);
    if (!assign_stmt) {
      printf("    Failed to create assignment for unsupported comparison operator %d\n", unsupported_ops[i]);
      all_success = false;
      break;
    }

    struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
    if (!body) {
      printf("    Failed to create body for unsupported comparison operator %d\n", unsupported_ops[i]);
      all_success = false;
      break;
    }
    body->stmt = assign_stmt;
    body->next = NULL;

    struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
    if (!py_kernel) {
      printf("    Failed to create kernel for unsupported comparison operator %d\n", unsupported_ops[i]);
      all_success = false;
      break;
    }

    // Should fail with appropriate error message
    if (!test_simplify_failure(py_kernel, expected_errors[i])) {
      printf("    Expected %s error for operator %d\n", expected_errors[i], unsupported_ops[i]);
      all_success = false;
      break;
    }
  }

  region_destroy(region);
  return all_success;
}

// Helper function to create a Python function call
static struct Python_Expr *make_python_call(const char *func_name,
                                            struct Python_Expr_List *args,
                                            struct region *region) {
  struct Python_Expr *func_expr = make_python_var(func_name, region);
  if (!func_expr)
    return NULL;

  struct Python_Expr *expr = region_alloc(region, sizeof(*expr));
  if (!expr)
    return NULL;

  expr->expr = region_alloc(region, sizeof(*expr->expr));
  if (!expr->expr)
    return NULL;

  expr->pos = make_python_pos(region);
  if (!expr->pos)
    return NULL;

  expr->expr->tag = Python_Expr_call;
  expr->expr->call.f = func_expr;
  expr->expr->call.args = args;
  expr->expr->call.keywords = NULL;

  return expr;
}

// Helper function to create an expression list
static struct Python_Expr_List *make_expr_list(struct Python_Expr *expr,
                                               struct Python_Expr_List *next,
                                               struct region *region) {
  struct Python_Expr_List *list = region_alloc(region, sizeof(*list));
  if (!list)
    return NULL;

  list->expr = expr;
  list->next = next;
  return list;
}

// Test 15: Function calls
static bool test_function_calls() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create function call: result = func(42)
  struct Python_Expr *arg = make_python_const_int(42, region);
  if (!arg) {
    region_destroy(region);
    return false;
  }

  struct Python_Expr_List *args = make_expr_list(arg, NULL, region);
  if (!args) {
    region_destroy(region);
    return false;
  }

  struct Python_Expr *call_expr = make_python_call("func", args, region);
  if (!call_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("result", call_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 16: Nested expressions
static bool test_nested_expressions() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create nested expression: result = (1 + 2) * (3 - 4)
  struct Python_Expr *const1 = make_python_const_int(1, region);
  struct Python_Expr *const2 = make_python_const_int(2, region);
  struct Python_Expr *const3 = make_python_const_int(3, region);
  struct Python_Expr *const4 = make_python_const_int(4, region);

  if (!const1 || !const2 || !const3 || !const4) {
    region_destroy(region);
    return false;
  }

  struct Python_Expr *add_expr = make_python_binop(Python_BinOp_add, const1, const2, region);
  struct Python_Expr *sub_expr = make_python_binop(Python_BinOp_sub, const3, const4, region);

  if (!add_expr || !sub_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Expr *mul_expr = make_python_binop(Python_BinOp_mul, add_expr, sub_expr, region);
  if (!mul_expr) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *assign_stmt = make_assignment("result", mul_expr, region);
  if (!assign_stmt) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = assign_stmt;
  body->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 17: Expression statements
static bool test_expression_statements() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create expression statement: func(42)
  struct Python_Expr *arg = make_python_const_int(42, region);
  if (!arg) {
    region_destroy(region);
    return false;
  }

  struct Python_Expr_List *args = make_expr_list(arg, NULL, region);
  if (!args) {
    region_destroy(region);
    return false;
  }

  struct Python_Expr *call_expr = make_python_call("func", args, region);
  if (!call_expr) {
    region_destroy(region);
    return false;
  }

  // Create expression statement
  struct Python_Stmt *expr_stmt = region_alloc(region, sizeof(*expr_stmt));
  if (!expr_stmt) {
    region_destroy(region);
    return false;
  }

  expr_stmt->stmt = region_alloc(region, sizeof(*expr_stmt->stmt));
  if (!expr_stmt->stmt) {
    region_destroy(region);
    return false;
  }

  expr_stmt->pos = make_python_pos(region);
  if (!expr_stmt->pos) {
    region_destroy(region);
    return false;
  }

  expr_stmt->stmt->tag = Python_Stmt_expr;
  expr_stmt->stmt->expr.e = call_expr;

  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = expr_stmt;
  body->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 18: Empty kernel (only pass statements)
static bool test_empty_kernel() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Create multiple pass statements
  struct Python_Stmt *pass1 = make_pass_stmt(region);
  struct Python_Stmt *pass2 = make_pass_stmt(region);

  if (!pass1 || !pass2) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt_List *body2 = region_alloc(region, sizeof(*body2));
  struct Python_Stmt_List *body1 = region_alloc(region, sizeof(*body1));
  if (!body1 || !body2) {
    region_destroy(region);
    return false;
  }

  body1->stmt = pass1;
  body1->next = body2;
  body2->stmt = pass2;
  body2->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body1, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 19: Complex assignment patterns
static bool test_complex_assignments() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test augmented assignment: x += 5
  struct Python_Expr *var_x = make_python_var("x", region);
  struct Python_Expr *const5 = make_python_const_int(5, region);

  if (!var_x || !const5) {
    region_destroy(region);
    return false;
  }

  struct Python_Stmt *aug_assign = region_alloc(region, sizeof(*aug_assign));
  if (!aug_assign) {
    region_destroy(region);
    return false;
  }

  aug_assign->stmt = region_alloc(region, sizeof(*aug_assign->stmt));
  if (!aug_assign->stmt) {
    region_destroy(region);
    return false;
  }

  aug_assign->pos = make_python_pos(region);
  if (!aug_assign->pos) {
    region_destroy(region);
    return false;
  }

  aug_assign->stmt->tag = Python_Stmt_augAssign;
  aug_assign->stmt->augAssign.x = var_x;
  aug_assign->stmt->augAssign.op = Python_BinOp_add;
  aug_assign->stmt->augAssign.e = const5;

  struct Python_Stmt_List *body = region_alloc(region, sizeof(*body));
  if (!body) {
    region_destroy(region);
    return false;
  }
  body->stmt = aug_assign;
  body->next = NULL;

  struct Python_Kernel *py_kernel = make_test_kernel("main", body, region);
  if (!py_kernel) {
    region_destroy(region);
    return false;
  }

  bool success = test_simplify_success(py_kernel);

  region_destroy(region);
  return success;
}

// Test 20: Edge cases and error conditions
static bool test_edge_cases() {
  struct region *region = create_test_region();
  if (!region)
    return false;

  // Test with empty function list (should fail)
  struct Python_Kernel *empty_kernel = region_alloc(region, sizeof(*empty_kernel));
  if (!empty_kernel) {
    region_destroy(region);
    return false;
  }

  empty_kernel->entry = "main";
  empty_kernel->funcs = NULL;  // No functions
  empty_kernel->args = NULL;
  empty_kernel->kwargs = NULL;
  empty_kernel->globals = NULL;
  empty_kernel->undefinedSymbols = NULL;

  // Should fail because entry function is not found
  bool success = test_simplify_failure(empty_kernel, "entry function");

  region_destroy(region);
  return success;
}

int main() {
  printf("Running comprehensive simplify module tests...\n\n");

  // Basic functionality tests
  TEST(null_input_handling);
  TEST(constant_conversion);
  TEST(different_constants);
  TEST(string_constants);
  TEST(float_constants);
  TEST(variable_handling);

  // Operator tests
  TEST(binary_operations);
  TEST(supported_binary_operators);
  TEST(unsupported_operators);
  TEST(unary_operators);
  TEST(comparison_operators);
  TEST(unsupported_comparison_operators);

  // Expression tests
  TEST(function_calls);
  TEST(nested_expressions);

  // Statement tests
  TEST(expression_statements);
  TEST(multiple_statements);
  TEST(complex_assignments);
  TEST(empty_kernel);

  // Error handling tests
  TEST(entry_function_not_found);
  TEST(edge_cases);

  printf("\n=== Test Results ===\n");
  printf("Tests run: %d\n", tests_run);
  printf("Tests passed: %d\n", tests_passed);
  printf("Tests failed: %d\n", tests_run - tests_passed);

  if (tests_passed == tests_run) {
    printf("\n🎉 All tests PASSED! 🎉\n");
    printf("The simplify module is working correctly.\n");
    return 0;
  } else {
    printf("\n❌ Some tests FAILED! ❌\n");
    printf("Please review the failed tests above.\n");
    return 1;
  }
}
