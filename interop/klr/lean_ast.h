#pragma once

#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

lean_object* Core_Pos_mk(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
lean_object* Python_Const_bool(uint8_t);
lean_object* Python_Const_int(lean_object*);
lean_object* Python_Const_float(double);
lean_object* Python_Const_string(lean_object*);
lean_object* Python_Const_tensor(lean_object*,lean_object*);
extern lean_object* Python_Const_none;
extern lean_object* Python_Const_ellipsis;
lean_object* Python_Keyword_mk(lean_object*,lean_object*,lean_object*);
extern uint8_t Python_Ctx_load;
extern uint8_t Python_Ctx_store;
extern uint8_t Python_Ctx_del;
lean_object* Python_Expr_mk(lean_object*,lean_object*);
lean_object* Python_Kernel_mk(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
lean_object* Python_Class_mk(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
lean_object* Python_Stmt_expr(lean_object*);
lean_object* Python_Stmt_assert(lean_object*);
lean_object* Python_Stmt_ret(lean_object*);
lean_object* Python_Stmt_assign(lean_object*,lean_object*);
lean_object* Python_Stmt_augAssign(lean_object*,uint8_t,lean_object*);
lean_object* Python_Stmt_annAssign(lean_object*,lean_object*,lean_object*);
lean_object* Python_Stmt_ifStm(lean_object*,lean_object*,lean_object*);
lean_object* Python_Stmt_forLoop(lean_object*,lean_object*,lean_object*,lean_object*);
lean_object* Python_Stmt_whileLoop(lean_object*,lean_object*,lean_object*);
extern lean_object* Python_Stmt_pass;
extern lean_object* Python_Stmt_breakLoop;
extern lean_object* Python_Stmt_continueLoop;
lean_object* Python_Expr_const(lean_object*);
lean_object* Python_Expr_name(lean_object*,uint8_t);
lean_object* Python_Expr_attr(lean_object*,lean_object*,uint8_t);
lean_object* Python_Expr_tuple(lean_object*,uint8_t);
lean_object* Python_Expr_list(lean_object*,uint8_t);
lean_object* Python_Expr_dict(lean_object*,lean_object*);
lean_object* Python_Expr_subscript(lean_object*,lean_object*,uint8_t);
lean_object* Python_Expr_slice(lean_object*,lean_object*,lean_object*);
lean_object* Python_Expr_boolOp(uint8_t,lean_object*);
lean_object* Python_Expr_binOp(uint8_t,lean_object*,lean_object*);
lean_object* Python_Expr_unaryOp(uint8_t,lean_object*);
lean_object* Python_Expr_compare(lean_object*,lean_object*,lean_object*);
lean_object* Python_Expr_ifExp(lean_object*,lean_object*,lean_object*);
lean_object* Python_Expr_call(lean_object*,lean_object*,lean_object*);
lean_object* Python_Expr_starred(lean_object*,uint8_t);
lean_object* Python_Expr_object(lean_object*,lean_object*);
lean_object* Python_Expr_format(lean_object*,lean_object*);
lean_object* Python_Expr_joined(lean_object*);
extern uint8_t Python_UnaryOp_invert;
extern uint8_t Python_UnaryOp_not;
extern uint8_t Python_UnaryOp_uadd;
extern uint8_t Python_UnaryOp_usub;
lean_object* Python_Fun_mk(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
extern uint8_t Python_BoolOp_land;
extern uint8_t Python_BoolOp_lor;
lean_object* Python_Args_mk(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
lean_object* Python_Stmt_mk(lean_object*,lean_object*);
extern uint8_t Python_CmpOp_eq;
extern uint8_t Python_CmpOp_ne;
extern uint8_t Python_CmpOp_lt;
extern uint8_t Python_CmpOp_le;
extern uint8_t Python_CmpOp_gt;
extern uint8_t Python_CmpOp_ge;
extern uint8_t Python_CmpOp_is;
extern uint8_t Python_CmpOp_isNot;
extern uint8_t Python_CmpOp_isIn;
extern uint8_t Python_CmpOp_notIn;
extern uint8_t Python_BinOp_add;
extern uint8_t Python_BinOp_sub;
extern uint8_t Python_BinOp_mul;
extern uint8_t Python_BinOp_matmul;
extern uint8_t Python_BinOp_div;
extern uint8_t Python_BinOp_mod;
extern uint8_t Python_BinOp_pow;
extern uint8_t Python_BinOp_lshift;
extern uint8_t Python_BinOp_rshift;
extern uint8_t Python_BinOp_or;
extern uint8_t Python_BinOp_xor;
extern uint8_t Python_BinOp_and;
extern uint8_t Python_BinOp_floor;

#ifdef __cplusplus
}
#endif
