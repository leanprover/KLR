/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "frontend.h"
#include "ast_python.h"
#include "ast_python_core.h"

/*
-- Gather
-- fetch all of the data we need from the Python environment

This code is a port of the code in interop/klr/parser.py and KLR/Python.lean.
This code runs in a "State Monad" similar to KLR.Python.Parsing.Parser but with
some additions for the work-list management.

This code is almost entirely structural. The only interesting thing this code
does is in the handling of name and attribute expressions, where it will find
references to other code and recursively load the referenced code. It is not
worth trying to generate this code from Lean, because we have to deal with the
cpython internal types. Longer term, we will replace the parser and then we can
extract this pass directly from Lean. In the meantime, here is some
old-world--style, hand-made, artisanal C code.
*/

struct state {
  // Memory region containing all data from this pass
  // (including the elements of this structure)
  struct region *region;

  // Functions to be processed
  struct worklist {
    struct worklist *next;
    const char *name;
    PyObject *f;
  } *work;

  // Set of processed functions
  struct Python_Fun_List *funs;

  // Set of resolved globals
  struct Python_Keyword_List *globals;

  // Current function scope
  struct scope {
    PyObject *f;       // python function we are working on
    char *src;         // source code of `f` (in region)
    char *file;        // filename where `f` lives (in region)
    u32 line_offset;   // line number in `file` where `f` lives
    u32 pad;
    // Current AST node location
    struct pos {
      u32 line, col;
    } pos;
  } scope;
};

// Generate a (Python) syntax error at the current location
// During the gather phase we use the Python syntax error exception
// to report errors. In later phases we create our own error messages.
// Note: if we get an error while building the error, the user will get
// error we got here, e.g. NoMemory, etc.

static void syntax_error(const struct state *st, const char *msg) {
  PyObject *msg_obj = PyUnicode_FromString(msg);
  if (!msg_obj)
    return;

  PyObject *args = PyTuple_Pack(1, msg_obj);
  Py_DECREF(msg_obj);
  if (!args)
    return;

  PyErr_SetObject(PyExc_SyntaxError, args);
  Py_DECREF(args);

  if (st->scope.file) {
    PyErr_SyntaxLocationEx(st->scope.file,
        st->scope.line_offset + st->scope.pos.line - 1,
        st->scope.pos.col);
  }
}

// returns true if we are having fun... if we have function `name`
static bool have_fun(const struct state *st, const char *name) {
  for (struct Python_Fun_List *l = st->funs; l; l = l->next) {
    if (strcmp(l->fun->name, name) == 0)
      return true;
  }
  return false;
}

static bool have_global(const struct state *st, const char *name) {
  for (struct Python_Keyword_List *l = st->globals; l; l = l->next) {
    if (strcmp(l->keyword->id, name) == 0)
      return true;
  }
  return false;
}

// Copy a Python string to our memory region.
// Note: we disallow embedded NULLs (which can only show up in literals).
// Note: zero-length strings are represented as NULL, which can also
// indicate an error if AsUTF8AndSize set an exception.
static char* py_strdup(struct state *st, PyObject *obj) {
  Py_ssize_t sz = 0;
  const char *s = PyUnicode_AsUTF8AndSize(obj, &sz);
  if (!s || sz <= 0)
    return NULL;

  if (memchr(s, 0, sz)) {
    syntax_error(st, "embedded NULL in string");
    return NULL;
  }

  return region_strdup(st->region, s);
}

// Construct a path name from two strings.
static char* path_name(struct state *st, const char *m, const char *x) {
  if (!m || !x)
    return NULL;

  size_t m_sz = strlen(m);
  size_t x_sz = strlen(x);

  char *name = region_alloc(st->region, m_sz + x_sz + 2);
  memcpy(name, m, m_sz);
  name[m_sz] = '.';
  memcpy(name + m_sz + 1, x, x_sz);
  name[m_sz + x_sz + 1] = 0;
  return name;
}

// Construct a path name from two Python strings (in memory region)
static inline char* py_path_name(struct state *st, PyObject *m, PyObject *x) {
  if (!m || !x)
    return NULL;
  return path_name(st, PyUnicode_AsUTF8(m), PyUnicode_AsUTF8(x));
}

// Construct full name of python function (in memory region)
static char* py_fun_name(struct state *st, PyObject *f) {
  PyObject *module = PyObject_GetAttrString(f, "__module__");
  PyObject *name = PyObject_GetAttrString(f, "__name__");
  char *f_name = py_path_name(st, module, name);

  Py_XDECREF(module);
  Py_XDECREF(name);
  PyErr_Clear();
  return f_name;
}

// Add a new function to the work-list (if necessary)
// Note: we are ignoring possible errors from Python as this function
// is allowed to fail.
static void add_work(struct state *st, PyObject *f) {
  if (!PyFunction_Check(f))
    return;

  char *name = py_fun_name(st, f);
  if (!name)
    return;

  // skip nki functions (for now)
  // TODO: remove once we have our own namespace
  if (strncmp("nki", name, 3) == 0)
    return;

  if (have_fun(st, name))
    return;

  // Scan/Add to worklist
  for (struct worklist **work = &st->work;; work = &(*work)->next) {
    if (!*work) {
      struct worklist *node = region_alloc(st->region, sizeof(*node));
      node->next = NULL;
      node->name = name;
      node->f = f;
      *work = node;
      break;
    }
    if (strcmp((*work)->name, name) == 0)
      break;
  }
}

// Try to add a new global reference to the environment. Note, this is
// best-effort as we are not completely sure that we need the global (or even
// if this really is a global reference) at this point. Later passes will raise
// more intelligent errors, so we can simply fail to add the reference.
// See: KLR/Trace/Python.lean for more details.

static struct Python_Const* value(struct state *st, PyObject *obj);
static struct Python_Expr_List* const_exprs(struct state *st, PyObject *obj);

#define mkPos(p,a,b,c,d) { \
  p = region_alloc(st->region, sizeof(*(p))); \
  p->line = a; \
  p->lineEnd = b; \
  p->column = c; \
  p->columnEnd = d; \
  }
#define Pos(p,obj) mkPos(p, \
                         obj->lineno, obj->end_lineno, \
                         obj->col_offset, obj->end_col_offset)

static struct Python_Expr* const_expr(struct state *st, PyObject *obj) {
  struct Python_Expr *e = region_alloc(st->region, sizeof(*e));
  e->expr = region_alloc(st->region, sizeof(*e->expr));

  mkPos(e->pos, 0, 0, 0, 0);

  e->expr->c.value = value(st, obj);
  if (e->expr->c.value) {
    e->expr->tag = Python_Expr_const;
    return e;
  }

  // value may have set an exception, clear it
  PyErr_Clear();

  // Check for other types of supported global values
  if (PyTuple_Check(obj)) {
    e->expr->tag = Python_Expr_tuple;
    e->expr->tuple.xs = const_exprs(st, obj);
    e->expr->tuple.ctx = Python_Ctx_load;
    return e;
  }
  else if (PyList_Check(obj)) {
    e->expr->tag = Python_Expr_list;
    e->expr->list.xs = const_exprs(st, obj);
    e->expr->list.ctx = Python_Ctx_load;
    return e;
  }
  else if (PyModule_Check(obj)) {
    const char *name = PyModule_GetName(obj);
    if (!name) {
      PyErr_Clear();
      return NULL;
    }
    e->expr->tag = Python_Expr_name;
    e->expr->name.id = region_strdup(st->region, name);
    e->expr->name.ctx = Python_Ctx_load;
    return e;
  }
  else
  {
    // TODO handle numpy tensors
    return NULL;
  }

  return NULL;
}

// Note: in case of errors we will return an empty list (NULL)
static struct Python_Expr_List* const_exprs(struct state *st, PyObject *obj) {
  if (!obj)
    return NULL;

  Py_ssize_t sz = PyObject_Length(obj);
  if (sz <= 0) {
    PyErr_Clear();
    return NULL;
  }

  struct Python_Expr_List *head = NULL, *current = NULL;
  for (Py_ssize_t i = 0; i < sz; i++) {
    struct Python_Expr_List *node = region_alloc(st->region, sizeof(*node));

    PyObject *key = PyLong_FromLong(i);
    if (!key) {
      PyErr_Clear();
      return NULL;
    }

    // Note: Object_GetItem increments reference count
    PyObject *item = PyObject_GetItem(obj, key);
    Py_DECREF(key);
    if (!item) {
      PyErr_Clear();
      return NULL;
    }

    struct Python_Expr *e = const_expr(st, item);
    Py_DECREF(item);
    if (!e)
      return NULL;

    node->next = NULL;
    node->expr = e;
    if (!head) {
      head = current = node;
    } else {
      current->next = node;
      current = node;
    }
  }
  return head;
}

static void add_global(struct state *st, char *name, PyObject *obj) {
  if (!name || !obj)
    return;

  if (have_fun(st, name) || have_global(st, name))
    return;

  struct Python_Keyword_List *node = region_alloc(st->region, sizeof(*node));
  struct Python_Keyword *kw = region_alloc(st->region, sizeof(*kw));
  kw->value = const_expr(st, obj);
  if (kw->value) {
    kw->id = name;
    node->next = st->globals;
    node->keyword = kw;
    st->globals = node;
  }
}


// Lookup item `id` in dictionary `name` which should be an attribute of `f`.
// e.g. f.name['id']
static PyObject* lookup_(PyObject *f, const char *name, const char *id) {
  if (!f || !name || !id)
    return NULL;

  PyObject *dict = PyObject_GetAttrString(f, name);
  if (!dict) return NULL;

  PyObject *value = PyDict_GetItemString(dict, id);
  Py_DECREF(dict);

  if (value)
    Py_INCREF(value);
  return value;
}

// Lookup `id` in current function's environment
static PyObject* lookup(struct state *st, const char *id) {
  PyObject *obj = lookup_(st->scope.f, "__globals__", id);
  if (!obj)
    obj = lookup_(st->scope.f, "__builtins__", id);
  return obj;
}

// Record reference to expression `e`, which is either a name or an attribute,
// which we can think of as a pathname. For each element of the pathname, we
// lookup the name in the Python environment and either: add the value to our
// globals, or, if it is a function, add the function to our work list.

struct ref {
  char *name;
  PyObject *obj;
};

static struct ref reference(struct state *st, struct Python_Expr *e) {
  struct ref ref = { NULL, NULL };
  if (!e) return ref;

  switch(e->expr->tag) {
  case Python_Expr_name:
    ref.name = (char*)e->expr->name.id;
    ref.obj = lookup(st, e->expr->name.id);
    if (!ref.obj) {
      ref.name = NULL;
      break;
    }
    break;

  case Python_Expr_attr:
    ref = reference(st, e->expr->attr.value);
    if (!ref.obj) {
      ref.name = NULL;
      break;
    }

    if (PyObject_HasAttrString(ref.obj, e->expr->attr.id)) {
      ref.obj = PyObject_GetAttrString(ref.obj, e->expr->attr.id);
      ref.name = path_name(st, ref.name, e->expr->attr.id);
    } else {
      Py_DECREF(ref.obj);
      ref.name = NULL;
      ref.obj = NULL;
    }
    break;

  default:
    break;
  }

  if (ref.name && ref.obj) {
    if (PyFunction_Check(ref.obj))
      add_work(st, ref.obj);
    else
      add_global(st, ref.name, ref.obj);
  }
  PyErr_Clear(); // Make sure we don't report any errors
  return ref;
}

// -----------------------------------------------------------------------------
// -- Constants

// The Python AST stores constants as Python objects in the heap.
// TODO: We are restricting int and float types very early, which is different
// from how the Lean code works.

static struct Python_Const* value(struct state *st, PyObject *obj) {
  if (!st || !obj)
    return NULL;

  struct Python_Const *c = region_alloc(st->region, sizeof(*c));

  if (Py_IsNone(obj)) {
    c->tag = Python_Const_none;
  }
  else if (PyBool_Check(obj)) {
    c->tag = Python_Const_bool;
    c->b.value = Py_IsTrue(obj) != 0;
  }
  else if (PyLong_Check(obj)) {
    c->tag = Python_Const_int;
    int overflow = 0;
    long value = PyLong_AsLongAndOverflow(obj, &overflow);
    if (value == -1 && PyErr_Occurred()) {
      return NULL;
    }
    if (overflow < 0 || value < INT_MIN) {
      syntax_error(st, "integer value is too small");
      return NULL;
    }
    if (overflow > 0 || value > INT_MAX) {
      syntax_error(st, "integer value is too large");
      return NULL;
    }
    c->i.value = (i32)value;
  }
  else if (PyFloat_Check(obj)) {
    c->tag = Python_Const_float;
    double d = PyFloat_AsDouble(obj);
    if (PyErr_Occurred())
      return NULL;
    // TODO: Using C semantics, which is technically undefined in this case
    c->f.value = (float)d;
  }
  else if (PyUnicode_Check(obj)) {
    c->tag = Python_Const_string;
    c->s.value = py_strdup(st, obj);
    if (!c->s.value)
      return NULL;
  }
  else if (Py_IS_TYPE(obj, &PyEllipsis_Type)) {
    c->tag = Python_Const_ellipsis;
  }
  else {
    return NULL;
  }

  return c;
}

// -----------------------------------------------------------------------------
// -- Expressions

static enum Python_Ctx context(expr_context_ty ctx) {
  switch (ctx) {
  case Load: return Python_Ctx_load;
  case Store: return Python_Ctx_store;
  case Del: return Python_Ctx_del;
  default: return Python_Ctx_load;  // impossible (safe default)
  }
}

static enum Python_BoolOp boolop(boolop_ty op) {
  switch (op) {
  case And: return Python_BoolOp_land;
  case Or: return Python_BoolOp_lor;
  default: return (u32)-1; // impossible
  }
}

static enum Python_UnaryOp unaryop(unaryop_ty op) {
  switch (op) {
  case Invert: return Python_UnaryOp_invert;
  case Not: return Python_UnaryOp_not;
  case UAdd: return Python_UnaryOp_uadd;
  case USub: return Python_UnaryOp_usub;
  default: return (u32)-1; // impossible
  }
}

static enum Python_BinOp binop(operator_ty op) {
  switch (op) {
  case Add: return Python_BinOp_add;
  case Sub: return Python_BinOp_sub;
  case Mult: return Python_BinOp_mul;
  case MatMult: return Python_BinOp_matmul;
  case Div: return Python_BinOp_div;
  case Mod: return Python_BinOp_mod;
  case Pow: return Python_BinOp_pow;
  case LShift: return Python_BinOp_lshift;
  case RShift: return Python_BinOp_rshift;
  case BitOr: return Python_BinOp_or;
  case BitXor: return Python_BinOp_xor;
  case BitAnd: return Python_BinOp_and;
  case FloorDiv: return Python_BinOp_floor;
  default: return (u32)-1;  // impossible
  }
}

static enum Python_CmpOp cmpop(cmpop_ty op) {
  switch (op) {
  case Eq: return Python_CmpOp_eq;
  case NotEq: return Python_CmpOp_ne;
  case Lt: return Python_CmpOp_lt;
  case LtE: return Python_CmpOp_le;
  case Gt: return Python_CmpOp_gt;
  case GtE: return Python_CmpOp_ge;
  case Is: return Python_CmpOp_is;
  case IsNot: return Python_CmpOp_isNot;
  case In: return Python_CmpOp_isIn;
  case NotIn: return Python_CmpOp_notIn;
  default: return (u32)-1; // impossible
  }
}

static struct Python_CmpOp_List* cmpops(struct state *st, asdl_int_seq *ops) {
  if (!ops)
    return NULL;

  struct Python_CmpOp_List *head = NULL, *current = NULL;
  for (int i = 0; i < ops->size; i++) {
    struct Python_CmpOp_List *node = region_alloc(st->region, sizeof(*node));
    enum Python_CmpOp op = cmpop(ops->typed_elements[i]);
    if (op == (u32)-1)
      return NULL;

    node->next = NULL;
    node->cmpop = op;
    if (!head) {
      head = current = node;
    } else {
      current->next = node;
      current = node;
    }
  }
  return head;
}

static struct Python_Expr_List* exprs(struct state *st, asdl_expr_seq *python);
static struct Python_Keyword_List* keywords(struct state *st, asdl_keyword_seq *python);

static struct Python_Expr* expr(struct state *st, struct _expr *python) {
  if (!python)
    return NULL;

  struct pos old_pos = st->scope.pos;
  st->scope.pos.line = python->lineno;
  st->scope.pos.col = python->col_offset;

  struct Python_Expr *res = region_alloc(st->region, sizeof(*res));
  struct Python_Expr_ *e = res->expr = region_alloc(st->region, sizeof(*e));
  Pos(res->pos, python);

  switch (python->kind) {
    case Constant_kind: {
      e->tag = Python_Expr_const;
      e->c.value = value(st, python->v.Constant.value);
      if (!e->c.value)
        res = NULL;
      break;
    }
    // Names and attributes may be references which we need to track
    // We rely on the ctx value for a small optimization: we only need
    // to consider Loads
    case Name_kind: {
      e->tag = Python_Expr_name;
      e->name.id = py_strdup(st, python->v.Name.id);
      e->name.ctx = context(python->v.Name.ctx);
      if (!e->name.id) {
        res = NULL;
        break;
      }

      if (e->name.ctx == Python_Ctx_load)
        reference(st, res);
      break;
    }
    case Attribute_kind: {
      e->tag = Python_Expr_attr;
      e->attr.value = expr(st, python->v.Attribute.value);
      e->attr.id = py_strdup(st, python->v.Attribute.attr);
      e->attr.ctx = context(python->v.Attribute.ctx);
      if (!e->attr.value || !e->attr.id) {
        res = NULL;
        break;
      }

      if (e->attr.ctx == Python_Ctx_load)
        reference(st, res);
      break;
    }

    // Sequences: Tuple and List
    case Tuple_kind: {
      e->tag = Python_Expr_tuple;
      e->tuple.xs = exprs(st, python->v.Tuple.elts);
      e->tuple.ctx = context(python->v.Tuple.ctx);
      if (!e->tuple.xs)
        res = NULL;
      break;
    }
    case List_kind: {
      e->tag = Python_Expr_list;
      e->list.xs = exprs(st, python->v.List.elts);
      e->list.ctx = context(python->v.List.ctx);
      if (!e->list.xs)
        res = NULL;
      break;
    }

    // Index expressions
    case Subscript_kind: {
      e->tag = Python_Expr_subscript;
      e->subscript.tensor = expr(st, python->v.Subscript.value);
      e->subscript.index = expr(st, python->v.Subscript.slice);
      e->subscript.ctx = context(python->v.Subscript.ctx);
      if (!e->subscript.tensor || !e->subscript.index)
        res = NULL;
      break;
    }
    case Slice_kind: {
      e->tag = Python_Expr_slice;
      e->slice.l = expr(st, python->v.Slice.lower);
      e->slice.u = expr(st, python->v.Slice.upper);
      e->slice.step = expr(st, python->v.Slice.step);
      break;
    }

    // Operators
    case BoolOp_kind: {
      e->tag = Python_Expr_boolOp;
      e->boolOp.op = boolop(python->v.BoolOp.op);
      e->boolOp.values = exprs(st, python->v.BoolOp.values);
      if (!e->boolOp.values)
        res = NULL;
      break;
    }
    case BinOp_kind: {
      e->tag = Python_Expr_binOp;
      e->binOp.op = binop(python->v.BinOp.op);
      e->binOp.left = expr(st, python->v.BinOp.left);
      e->binOp.right = expr(st, python->v.BinOp.right);
      if (!e->binOp.left || !e->binOp.right)
        res = NULL;
      break;
    }
    case UnaryOp_kind: {
      e->tag = Python_Expr_unaryOp;
      e->unaryOp.op = unaryop(python->v.UnaryOp.op);
      e->unaryOp.operand = expr(st, python->v.UnaryOp.operand);
      if (!e->unaryOp.operand)
        res = NULL;
      break;
    }
    case Compare_kind: {
      e->tag = Python_Expr_compare;
      e->compare.left = expr(st, python->v.Compare.left);
      e->compare.ops = cmpops(st, python->v.Compare.ops);
      e->compare.comparators = exprs(st, python->v.Compare.comparators);
      if (!e->compare.left || !e->compare.ops || !e->compare.comparators)
        res = NULL;
      break;
    }

    // Condition expression
    case IfExp_kind: {
      e->tag = Python_Expr_ifExp;
      e->ifExp.test = expr(st, python->v.IfExp.test);
      e->ifExp.body = expr(st, python->v.IfExp.body);
      e->ifExp.orelse = expr(st, python->v.IfExp.orelse);
      if (!e->ifExp.test)
        res = NULL;
      break;
    }

    // Function calls
    case Call_kind: {
      e->tag = Python_Expr_call;
      e->call.f = expr(st, python->v.Call.func);
      e->call.args = exprs(st, python->v.Call.args);
      e->call.keywords = keywords(st, python->v.Call.keywords);
      if (!e->call.f)
        res = NULL;
      break;
    }

    default:
      syntax_error(st, "unsupported expression");
      res = NULL;
      break;
  }

  st->scope.pos = old_pos;
  return res;
}

static struct Python_Expr_List *exprs(struct state *st, asdl_expr_seq *python) {
  if (!python)
    return NULL;

  struct Python_Expr_List *head = NULL, *current = NULL;
  for (int i = 0; i < python->size; i++) {
    struct Python_Expr_List *node = region_alloc(st->region, sizeof(*node));
    struct Python_Expr *e = expr(st, python->typed_elements[i]);
    if (!e)
      return NULL;

    node->next = NULL;
    node->expr = e;
    if (!head) {
      head = current = node;
    } else {
      current->next = node;
      current = node;
    }
  }
  return head;
}

// -----------------------------------------------------------------------------
// -- Keywords

static struct Python_Keyword* keyword(struct state *st, keyword_ty python) {
  if (!python)
    return NULL;

  // Note, we store the position, but do not update the context
  // The next expression also has a position, and we do not check the
  // keyword id
  struct Python_Keyword *kw = region_alloc(st->region, sizeof(*kw));
  Pos(kw->pos, python);

  kw->id = py_strdup(st, python->arg);
  kw->value = expr(st, python->value);
  if (!kw->id || !kw->value)
    return NULL;

  return kw;
}

static struct Python_Keyword_List* keywords(struct state *st, asdl_keyword_seq *python) {
  if (!python)
    return NULL;

  struct Python_Keyword_List *head = NULL, *current = NULL;
  for (int i = 0; i < python->size; i++) {
    struct Python_Keyword_List *node = region_alloc(st->region, sizeof(*node));
    struct Python_Keyword *kw = keyword(st, python->typed_elements[i]);
    if (!kw)
      return NULL;

    node->next = NULL;
    node->keyword = kw;
    if (!head) {
      head = current = node;
    } else {
      current->next = node;
      current = node;
    }
  }
  return head;
}

// -----------------------------------------------------------------------------
// -- Arguments

static char* arg(struct state *st, arg_ty python) {
  if (!python)
    return NULL;
  char *s = py_strdup(st, python->arg);
  if (!s)
    PyErr_Clear();
  return s;
}

static struct String_List* arg_list(struct state *st, asdl_arg_seq *python) {
  if (!python)
    return NULL;

  struct String_List *head = NULL, *current = NULL;
  for (int i = 0; i < python->size; i++) {
    struct String_List *node = region_alloc(st->region, sizeof(*node));
    char *str = arg(st, python->typed_elements[i]);
    if (!str)
      return NULL;

    node->next = NULL;
    node->s = str;
    if (!head) {
      head = current = node;
    } else {
      current->next = node;
      current = node;
    }
  }
  return head;
}

static struct Python_Args* args(struct state *st, arguments_ty python) {
  if (!python)
    return NULL;

  // Note: process expressions last to avoid clearing errors
  struct Python_Args *as = region_alloc(st->region, sizeof(*as));
  as->posonlyargs = arg_list(st, python->posonlyargs);
  as->args = arg_list(st, python->args);
  as->vararg = arg(st, python->vararg);
  as->kwonlyargs = arg_list(st, python->kwonlyargs);
  as->kwarg = arg(st, python->kwarg);

  as->defaults = exprs(st, python->defaults);
  // TODO: this is a bug
  // The old version of gather computed the names of keyword defaults,
  // but this is not what the parser does.
  //as->kw_defaults = exprs(st, python->kw_defaults);
  as->kw_defaults = NULL;
  return as;
}

// -----------------------------------------------------------------------------
// -- Statements

static struct Python_Stmt_List* stmts(struct state *st, asdl_stmt_seq *python);

static struct Python_Stmt* stmt(struct state *st, struct _stmt *python) {
  if (!python)
    return NULL;

  struct pos old_pos = st->scope.pos;
  st->scope.pos.line = python->lineno;
  st->scope.pos.col = python->col_offset;

  struct Python_Stmt *res = region_alloc(st->region, sizeof(*res));
  struct Python_Stmt_ *s = res->stmt = region_alloc(st->region, sizeof(*s));
  Pos(res->pos, python);

  switch (python->kind) {
    case Pass_kind:
      s->tag = Python_Stmt_pass;
      break;

    // Simple expressions
    case Expr_kind: {
      s->tag = Python_Stmt_expr;
      s->expr.e = expr(st, python->v.Return.value);
      if (!s->expr.e)
        res = NULL;
      break;
    }
    case Assert_kind: {
      // TODO capture message
      s->tag = Python_Stmt_assert;
      s->assert.e = expr(st, python->v.Assert.test);
      if (!s->assert.e)
        res = NULL;
      break;
    }
    case Return_kind: {
      s->tag = Python_Stmt_ret;
      s->ret.e = expr(st, python->v.Return.value);
      if (!s->ret.e)
        res = NULL;
      break;
    }

    // Assignments
    case Assign_kind: {
      s->tag = Python_Stmt_assign;
      s->assign.xs = exprs(st, python->v.Assign.targets);
      s->assign.e = expr(st, python->v.Assign.value);
      if (!s->assign.xs || !s->assign.e)
        res = NULL;
      break;
    }
    case AugAssign_kind: {
      s->tag = Python_Stmt_augAssign;
      s->augAssign.op = binop(python->v.AugAssign.op);
      s->augAssign.x = expr(st, python->v.AugAssign.target);
      s->augAssign.e = expr(st, python->v.AugAssign.value);
      if (!s->augAssign.x || !s->augAssign.e)
        res = NULL;
      break;
    }
    case AnnAssign_kind: {
      s->tag = Python_Stmt_annAssign;
      s->annAssign.x = expr(st, python->v.AnnAssign.target);
      s->annAssign.annotation = expr(st, python->v.AnnAssign.annotation);
      s->annAssign.value = expr(st, python->v.AnnAssign.value);
      if (!s->annAssign.x || !s->annAssign.annotation)
        res = NULL;
      break;
    }

    // If statements
    case If_kind: {
      s->tag = Python_Stmt_ifStm;
      s->ifStm.e = expr(st, python->v.If.test);
      if (s->ifStm.e) {
        // Note: we allow both to be empty
        s->ifStm.thn = stmts(st, python->v.If.body);
        s->ifStm.els = stmts(st, python->v.If.orelse);
      } else {
        res = NULL;
      }
      break;
    }

    // For loops
    case For_kind: {
      s->tag = Python_Stmt_forLoop;
      s->forLoop.x = expr(st, python->v.For.target);
      s->forLoop.iter = expr(st, python->v.For.iter);
      if (s->forLoop.x && s->forLoop.iter) {
        // Note: we allow both to be empty
        s->forLoop.body = stmts(st, python->v.For.body);
        s->forLoop.orelse = stmts(st, python->v.For.orelse);
      } else {
        res = NULL;
      }
      break;
    }
    case Break_kind: {
      s->tag = Python_Stmt_breakLoop;
      break;
    }
    case Continue_kind: {
      s->tag = Python_Stmt_continueLoop;
      break;
    }

    // TODO: syntax extensions we need to add
    case While_kind:
    case With_kind:
    default:
      syntax_error(st, "unsupported statement");
      res = NULL;
      break;
  }
  st->scope.pos = old_pos;
  return res;
}

static struct Python_Stmt_List* stmts(struct state *st, asdl_stmt_seq *python) {
  if (!python)
    return NULL;

  struct Python_Stmt_List *head = NULL, *current = NULL;
  for (int i = 0; i < python->size; i++) {
    struct Python_Stmt_List *node = region_alloc(st->region, sizeof(*node));
    struct Python_Stmt *stm = stmt(st, python->typed_elements[i]);
    if (!stm)
      return NULL;

    node->next = NULL;
    node->stmt = stm;
    if (!head) {
      head = current = node;
    } else {
      current->next = node;
      current = node;
    }
  }
  return head;
}

// -----------------------------------------------------------------------------
// -- Interface to the parser

static PyObject* get_util(const char *name) {
  PyObject *f = NULL;
  PyObject *fe = PyUnicode_FromString("klr.frontend");
  if (fe) {
    PyObject *m = PyImport_GetModule(fe);
    if (m) {
      f = PyObject_GetAttrString(m, name);
      Py_DECREF(m);
    }
    Py_DECREF(fe);
  }
  return f;
}

static struct _mod* parse_function(struct state *st, PyObject *f) {
  // Initialization needed for done label
  struct _mod *m = NULL;
  PyObject *source = NULL;

  PyObject *getsrc = get_util("_get_src");
  PyObject *args = PyTuple_Pack(1, f);
  if (!getsrc || !args)
    goto done;

  source = PyObject_CallObject(getsrc, args);
  if (!source || !PyTuple_Check(source) || PyTuple_Size(source) != 3)
    goto done;

  // Note: Tuple_GetItem does not increment reference count
  PyObject *file = PyTuple_GetItem(source, 0);
  PyObject *line = PyTuple_GetItem(source, 1);
  PyObject *src  = PyTuple_GetItem(source, 2);

  if (!file || !PyUnicode_Check(file) ||
      !line || !PyLong_Check(line) ||
      !src  || !PyUnicode_Check(src))
    goto done;

  char *file_str = py_strdup(st, file);
  char *src_str = py_strdup(st, src);
  if (!file_str || !src_str)
    goto done;

  m = parse_string(src_str, file);
  if (m) {
    // everything checks out, enter new function scope
    st->scope.f = f;
    st->scope.src = src_str;
    st->scope.file = file_str;
    st->scope.line_offset = PyLong_AsLong(line);
    st->scope.pos.line = 0;
    st->scope.pos.col = 0;
  }

done:
  Py_XDECREF(getsrc);
  Py_XDECREF(args);
  Py_XDECREF(source);
  return m;
}

static struct Python_Fun* function(struct state *st, PyObject *f) {
  struct scope old_scope = st->scope;
  struct _mod *m = parse_function(st, f);

  if (!m ||
      m->kind != Interactive_kind ||
      !m->v.Interactive.body ||
      m->v.Interactive.body->size != 1 ||
      m->v.Interactive.body->typed_elements[0]->kind != FunctionDef_kind
      )
  {
    st->scope = old_scope;
    return NULL;
  }

  struct _stmt *s = m->v.Interactive.body->typed_elements[0];
  struct Python_Args *as = args(st, s->v.FunctionDef.args);

  struct Python_Stmt_List *body = stmts(st, s->v.FunctionDef.body);
  free_python_ast(m);

  char *name = py_fun_name(st, f);
  struct Python_Fun *fn = NULL;
  if (as && body && name) {
    fn = region_alloc(st->region, sizeof(*fn));
    fn->name = name;
    fn->line = st->scope.line_offset;
    fn->source = st->scope.src;
    fn->body = body;
    fn->args = as;
  }

  st->scope = old_scope;
  return fn;
}

// -- Entry points

bool gather(struct kernel *k) {
  struct state st = {
    .region = region_create(),
    .work = NULL,
    .funs = NULL,
    .globals = NULL,
    .scope = { 0 }
  };

  add_work(&st, k->f);

  bool result = true;
  while (true) {
    struct worklist *work = st.work;
    if (!work) break;
    st.work = work->next;

    struct Python_Fun *f = function(&st, work->f);
    if (!f) {
      result = false;
      break;
    }
    struct Python_Fun_List *node = region_alloc(st.region, sizeof(*node));
    node->fun = f;
    node->next = st.funs;
    st.funs = node;
  }

  if (result) {
    struct Python_Kernel *python = region_alloc(st.region, sizeof(*python));
    python->entry = py_fun_name(&st, k->f);
    python->funcs = st.funs;
    python->args = NULL; // filled in by specialize
    python->globals = st.globals;
    python->kwargs = NULL; // filled in by specialize
    python->undefinedSymbols = NULL; // TODO

    k->python_region = st.region;
    k->python_kernel = python;
  }
  return result;
}

bool specialize(struct kernel *k, PyObject *args, PyObject *kws) {
  if (!k || !k->python_region) {
    PyErr_SetString(PyExc_RuntimeError, "No valid kernel for specialize");
    return false;
  }

  struct state st = {
    .region = k->python_region,
    .work = NULL,
    .funs = NULL,
    .globals = NULL,
    .scope = { 0 }
  };

  if (args) {
    if (!PyTuple_Check(args)) {
      PyErr_SetString(PyExc_ValueError, "Invalid arguments: args is not a tuple");
      return false;
    }
    struct Python_Expr_List **es = &k->python_kernel->args;
    Py_ssize_t size = PyTuple_Size(args);
    for (Py_ssize_t i = 0; i < size; i++) {
      // Note PyTuple_GetItem returns a borrowed reference
      PyObject *arg = PyTuple_GetItem(args, i);
      struct Python_Expr *e = const_expr(&st, arg);
      if (!e) {
        PyErr_Format(PyExc_ValueError, "%S is not a supported NKI type", arg);
        return false;
      }
      *es = region_alloc(st.region, sizeof(**es));
      (*es)->expr = e;
      (*es)->next = NULL;
      es = &(*es)->next;
    }
  }

  if (kws) {
    if (!PyDict_Check(kws)) {
      PyErr_SetString(PyExc_ValueError, "Invalid arguments: kwargs is not a dictionary");
      return false;
    }

    struct Python_Keyword_List **kw = &k->python_kernel->kwargs;
    Py_ssize_t pos = 0;
    PyObject *key, *val;
    while (PyDict_Next(kws, &pos, &key, &val)) {
      char *s = py_strdup(&st, key);
      if (!s)
        return false;

      struct Python_Expr *e = const_expr(&st, val);
      if (!e) {
        PyErr_Format(PyExc_ValueError, "%S is not a supported NKI type", val);
        return NULL;
      }

      *kw = region_alloc(st.region, sizeof(**kw));
      (*kw)->keyword = region_alloc(st.region, sizeof(struct Python_Keyword));
      (*kw)->keyword->pos = region_alloc(st.region, sizeof(struct Core_Pos));
      (*kw)->keyword->id = s;
      (*kw)->keyword->value = e;
      (*kw)->keyword->pos->line = 0;
      (*kw)->keyword->pos->column = 0;
      (*kw)->keyword->pos->lineEnd = 0;
      (*kw)->keyword->pos->columnEnd = 0;
      (*kw)->next = NULL;
      kw = &(*kw)->next;
    }
  }
  return true;
}
