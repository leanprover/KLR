/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "lean_ast.h"
#include "frontend.h"
#include "ast_python.h"

/*
-- Gather
-- fetch all of the data we need from the Python environment

This code is almost entirely structural. The only interesting thing this code
does is in the handling of name and attribute expressions, where it will find
references to other code and recursively load the referenced code.

Error handling.

In general, all functions in this file will always return a valid result. In
the case of errors, the result may be a place-holder such as None, Pass, or an
empty list. All errors and warnings are tracked in the messages field of the
state structure. If errors are reported, the final lean objects will be
collected and not returned. This strategy allows us to return multuple errors,
and simplifies a lot of the code (which doesn't need to check for errors).
*/

struct lean_kernel {
  lean_object *kernel;
};

struct state {
  // Memory region containing all data from this pass
  // (including the elements of this structure)
  struct region *region;

  // if true, do not follow references
  bool ignore_refs;

  // definitions to be processed (in region)
  struct worklist {
    struct worklist *next;
    const char *name;  // this is in the Lean heap
    lean_object *str;  // this is the string "name"
    PyObject *obj;
  } *work;

  // Set of processed definitions (in region)
  struct definition {
    struct definition *next;
    const char *name; // this is in the Lean heap
    lean_object *str; // this is the string "name"
    enum { FUN, CLS, GLOBAL } type;
    lean_object *obj; // type: Fun, Cls, Keyword, or NULL
  } *defs;

  // List of errors and warnings (in region)
  u32 errors, warnings;
  struct message {
    struct message *next;
    bool isError;
    const char *file;    // this is in the region
    u32 line, col;
    const char *message; // this is in the region
  } *messages, *msg_tail;

  // Current class/function scope (on stack)
  struct scope {
    PyObject *cls;     // python class we are working on
    PyObject *f;       // python function we are working on
    lean_object *src;  // source code of definition
    lean_object *file; // filename where definition lives
    u32 line_offset;   // line number in `file` where definition lives
    u32 pad;
    // Current AST node location
    struct pos {
      u32 line, col;
    } pos;
    // Local variables
    struct local {
      struct local *next;
      const char *name;   // this is in the Lean heap
    } *locals;
  } scope;
};

static void add_msg(struct state *st, bool isError, const char *fmt, ...) {
  if (isError && st->errors >= 100) return;
  if (!isError && st->warnings >= 10000) return;

  va_list args;
  va_start(args, fmt);

  // Note: vsnprintf will always create a null terminated string,
  char *buf;
  if (vasprintf(&buf, fmt, args) < 0) {
    perror("internal error");
    buf = strdup("internal error");
  }

  struct message *m = region_alloc(st->region, sizeof(*m));
  m->next = NULL;
  if (isError) {
    st->errors++;
    m->isError = true;
  } else {
    st->warnings++;
    m->isError = false;
  }
  if (st->scope.file) {
    m->file = region_strdup(st->region, lean_string_cstr(st->scope.file));
  } else {
    m->file = region_strdup(st->region, "<unknown>");
  }
  m->line = st->scope.line_offset + st->scope.pos.line;
  m->col = st->scope.pos.col;
  m->message = region_strdup(st->region, buf);
  free(buf);

  if (!st->msg_tail) {
    st->messages = m;
  } else {
    st->msg_tail->next = m;
  }
  st->msg_tail = m;
  va_end(args);
}

#define warn (st, ...) add_msg(st, false, __VA_ARGS__)
#define error(st, ...) add_msg(st, true,  __VA_ARGS__)

// Check for python exceptions. If cound emit warnings and clear.
static void checkPyErr(struct state *st) {
  if (!PyErr_Occurred())
    return;

  PyObject *ty = NULL, *e = NULL, *tr = NULL, *str = NULL;
  PyErr_Fetch(&ty, &e, &tr);

  if (e)
    str = PyObject_Str(e);

  Py_XDECREF(ty);
  Py_XDECREF(e);
  Py_XDECREF(tr);

  const char *s = PyUnicode_AsUTF8(str);
  Py_XDECREF(str);
  PyErr_Clear();  // str() or AsUTF8 could have raised an exception: ignore

  if (s)
    add_msg(st, false, s);
}

static bool have_def(const struct state *st, const char *name) {
  if (!name)
    return false;

  for (struct local *l = st->scope.locals; l; l = l->next) {
    if (strcmp(l->name, name) == 0)
      return true;
  }

  for (struct definition *d = st->defs; d; d = d->next) {
    if (strcmp(d->name, name) == 0)
      return true;
  }
  return false;
}

// Copy a Python string to the Lean heap.
// returns an empty string on error
static lean_object* py_strdup(struct state *st, PyObject *obj) {
  if (!obj) {
    error(st, "failed to convert string object");
    return lean_mk_string("");
  }

  PyErr_Clear();
  Py_ssize_t sz = -1;
  const char *s = PyUnicode_AsUTF8AndSize(obj, &sz);
  if (!s || sz < 0 || PyErr_Occurred()) {
    PyErr_Clear();
    error(st, "failed to convert string object");
    return lean_mk_string("");
  }

  return lean_mk_string_from_bytes(s, sz);
}

static lean_object* path_append(struct state *st, lean_object *base, PyObject *obj) {
  lean_object *dot = lean_mk_string(".");
  lean_object *lid = py_strdup(st, obj);
  lean_object *tmp = lean_string_append(base, dot);
  lean_object *res = lean_string_append(tmp, lid);
  lean_dec(dot);
  lean_dec(lid);
  return res;
}

// Construct a path name from two Python strings
static inline lean_object* py_path_name(struct state *st, PyObject *m, PyObject *x) {
  lean_object *base = py_strdup(st, m);
  lean_object *res = path_append(st, base, x);
  return res;
}

// Construct full name of python function or class
static lean_object* py_def_name(struct state *st, PyObject *f) {
  PyObject *module = PyObject_GetAttrString(f, "__module__");
  PyObject *name = PyObject_GetAttrString(f, "__name__");

  lean_object *f_name = py_path_name(st, module, name);

  Py_XDECREF(module);
  Py_XDECREF(name);
  return f_name;
}

// Construct full name of python method
static lean_object* py_method_name(struct state *st, lean_object *clsname, PyObject *f) {
  if (!f) {
    error(st, "could not get name of function");
    return lean_mk_string("");
  }
  PyObject *name = PyObject_GetAttrString(f, "__name__");

  lean_inc(clsname);
  lean_object *m_name = path_append(st, clsname, name);

  Py_XDECREF(name);
  return m_name;
}

// Add a new item to the work-list (if necessary)
// Note: we are ignoring possible errors from Python as this function
// is allowed to fail.
static void add_work(struct state *st, PyObject *obj) {
  if (!obj) return;

  lean_object *str = py_def_name(st, obj);
  const char *name = lean_string_cstr(str);
  if (name[0] == 0)
    return;

  // skip numpy (for performance)
  if (strncmp("numpy.", name, 6) == 0) {
    lean_dec(str);
    return;
  }

  // skip enum (for correctness)
  if (strncmp("enum.", name, 5) == 0) {
    lean_dec(str);
    return;
  }

  if (have_def(st, name)) {
    lean_dec(str);
    return;
  }

  // Scan/Add to worklist
  for (struct worklist **work = &st->work;; work = &(*work)->next) {
    if (!*work) {
      struct worklist *node = region_alloc(st->region, sizeof(*node));
      node->next = NULL;
      node->name = name;
      node->str = str;
      node->obj = obj;
      *work = node;
      break;
    }
    if (strcmp((*work)->name, name) == 0) {
      lean_dec(str);
      break;
    }
  }
}

// -- functions for building basic types

static inline lean_object* mkNone() {
  return lean_box(0);
}

static lean_object* mkSome(lean_object *obj) {
  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, obj);
  return some;
}

static inline lean_object* mkOption(lean_object *obj) {
  return obj ? mkSome(obj) : mkNone();
}

static inline lean_object* mkNil() {
  return lean_box(0);
}

static inline lean_object*
mkPos(unsigned line, unsigned column,
      unsigned lineEnd, unsigned columnEnd,
      lean_object *filename)
{
  return Core_Pos_mk(
    lean_unsigned_to_nat(line),
    lean_unsigned_to_nat(column),
    mkOption(lean_unsigned_to_nat(lineEnd)),
    mkOption(lean_unsigned_to_nat(columnEnd)),
    mkOption(filename));
}

static inline lean_object* curPos(struct state *st) {
  return mkPos(st->scope.pos.line, st->scope.pos.col,
               st->scope.pos.line, st->scope.pos.col,
               st->scope.file);
}

#define Pos(obj) \
  ((obj) ? \
    mkPos(obj->lineno, obj->end_lineno, \
          obj->col_offset, obj->end_col_offset, st->scope.file) : \
    mkPos(0,0,0,0, st->scope.file))


static lean_object* value(struct state *st, PyObject *obj);
static lean_object* const_exprs(struct state *st, PyObject *obj);
static lean_object* nat_list(struct state *st, PyObject *obj);

// Check if object is a tensor type
static bool is_tensor(PyObject *obj) {
  if (!obj) return false;

  PyTypeObject *t = Py_TYPE(obj);
  if (!t) return false;

  return strcmp(t->tp_name, "tensor") == 0 ||         // nki
         strcmp(t->tp_name, "numpy.ndarray") == 0 ||  // numpy
         strcmp(t->tp_name, "Tensor") == 0 ||         // PyTorch
         strcmp(t->tp_name, "ShapedArray") == 0;      // JAX
}

// Handle tensor objects (return Const)
static lean_object* tensor_const(struct state *st, PyObject *obj) {
  lean_object *sh = NULL;
  lean_object *dty = NULL;

  if (!obj) goto error;

  PyObject *shape = PyObject_GetAttrString(obj, "shape");
  if (!shape) goto error;
  sh = nat_list(st, shape);
  Py_DECREF(shape);

  PyObject *dtype = PyObject_GetAttrString(obj, "dtype");
  if (!dtype) goto error;

  PyObject *dstr = PyObject_Str(dtype);
  Py_DECREF(dtype);
  if (!dstr) goto error;

  dty = py_strdup(st, dstr);
  Py_DECREF(dstr);

  return Python_Const_tensor(sh, dty);

error:
  if (sh) lean_dec(sh);
  if (dty) lean_dec(dty);
  error(st, "could not convert tensor value");
  return Python_Const_none;
}

// This function never raises exceptions
// Returns a new reference
static PyObject* get_numpy_generic_dtype() {
  // Try to get already imported numpy module
  PyObject *numpy_name = PyUnicode_FromString("numpy");
  PyErr_Clear();
  if (!numpy_name) return NULL;

  PyObject *numpy = PyImport_GetModule(numpy_name);
  Py_DECREF(numpy_name);
  if (!numpy) {
    PyErr_Clear();
    return NULL;
  }

  // Get numpy.generic class
  PyObject *generic_class = PyObject_GetAttrString(numpy, "generic");
  Py_DECREF(numpy);
  if (!generic_class) {
    PyErr_Clear();
    return NULL;
  }
  return generic_class;
}

// Check if object is numpy dtype, if it is, then return the object
// This function never raises exceptions
static bool is_numpy_dtype(PyObject *obj) {
  if (!obj) return false;

  PyObject *generic_dtype = get_numpy_generic_dtype();
  if (!generic_dtype) return false;

  // Check if obj is instance of numpy.generic or subclass
  int result = PyObject_IsSubclass(obj, generic_dtype);
  Py_DECREF(generic_dtype);
  return result == 1;
}

// Check if object is numpy dtype instance, if it is, then return dtype object
// The user is responsible for decrementing a ref count on object returned
// if object is not null
//
// This function never raises exceptions
// Returns a new reference
static PyObject* numpy_dtype_instance(PyObject *obj) {
  if (!obj) return NULL;

  // NOTE: order matters here. If attemting to get type attr from
  // object before attempting to import numpy the object comes out
  // blank
  PyObject *generic_dtype = get_numpy_generic_dtype();
  if (!generic_dtype) return NULL;

  PyObject* obj_type = PyObject_GetAttrString(obj, "type");
  if (!obj_type) {
    PyErr_Clear();
    Py_DECREF(generic_dtype);
    return NULL;
  }

  // Check if obj is instance of numpy.generic or subclass
  int result = PyObject_IsSubclass(obj_type, generic_dtype);
  Py_DECREF(generic_dtype);

  if (result == 1) { // it's -1 when it's false
    return obj_type;
  }

  Py_DECREF(obj_type);
  return NULL;
}

static const char* suggest_nki_dtype(PyObject *obj) {
  if (!obj) return NULL;

  const char* t = ((PyTypeObject*)obj)->tp_name;
  if (!t) return NULL;

  if (strstr(t, "numpy.uint8")) return "nki.language.uint8";
  if (strstr(t, "numpy.int8")) return "nki.language.int8";
  if (strstr(t, "numpy.uint16")) return "nki.language.uint16";
  if (strstr(t, "numpy.int16")) return "nki.language.int16";
  if (strstr(t, "numpy.uint32")) return "nki.language.uint32";
  if (strstr(t, "numpy.int32")) return "nki.language.int32";
  if (strstr(t, "numpy.float16")) return "nki.language.float16";
  if (strstr(t, "numpy.float32")) return "nki.language.float32";
  if (strstr(t, "numpy.bool")) return "nki.language.bool";

  return NULL;
}

static lean_object* const_dict(struct state *st, PyObject *obj);

// returns Expr
static lean_object* const_expr(struct state *st, PyObject *obj) {
  lean_object *pos = curPos(st);
  lean_object *e = NULL;
  PyObject *numpy_dt = NULL;

  if (!obj) {
    error(st, "count not convert constant expression");
  }
  if (PyTuple_Check(obj)) {
    lean_object *l = const_exprs(st, obj);
    e = Python_Expr_mk(Python_Expr_tuple(l, Python_Ctx_load), pos);
  }
  else if (PyList_Check(obj)) {
    lean_object *l = const_exprs(st, obj);
    e = Python_Expr_mk(Python_Expr_list(l, Python_Ctx_load), pos);
  }
  else if (PyDict_Check(obj)) {
    PyObject *keys = PyDict_Keys(obj);
    PyObject *vals = PyDict_Values(obj);

    lean_object *l_keys = const_exprs(st, keys);
    lean_object *l_vals = const_exprs(st, vals);

    Py_XDECREF(keys);
    Py_XDECREF(vals);

    e = Python_Expr_mk(Python_Expr_dict(l_keys, l_vals), pos);
  }
  else if (PyModule_Check(obj)) {
    PyObject *name = PyModule_GetNameObject(obj);
    e = Python_Expr_mk(Python_Expr_name(py_strdup(st, name), Python_Ctx_load), pos);
  }
  else if (is_tensor(obj)) {
    lean_object *c = tensor_const(st, obj);
    e = Python_Expr_mk(Python_Expr_const(c), pos);
  }
  else if (is_numpy_dtype(obj)) {
    const char* nki_dtype = suggest_nki_dtype(obj);
    if (nki_dtype) {
      error(st, "numpy dtypes are not supported as arguments. Use %s instead", nki_dtype);
    } else {
      error(st, "numpy dtypes are not supported as arguments");
    }
  }
  else if ((numpy_dt = numpy_dtype_instance(obj)) && numpy_dt) {
    const char* nki_dtype = suggest_nki_dtype(numpy_dt);
    if (nki_dtype) {
      error(st, "numpy dtypes are not supported as arguments. Use %s instead", nki_dtype);
      Py_DECREF(numpy_dt);
    } else {
      error(st, "numpy dtypes are not supported as arguments");
    }
  }
  else if (PyObject_HasAttrString(obj, "__class__") &&
           PyObject_HasAttrString(obj, "__dict__"))
  {
    // general object types
    PyObject *cls = PyObject_GetAttrString(obj, "__class__");
    PyObject *dict = PyObject_GetAttrString(obj, "__dict__");

    lean_object *cls_name = py_def_name(st, cls);
    lean_object *l_dict = const_dict(st, dict);
    Py_XDECREF(dict);

    add_work(st, cls);
    e = Python_Expr_mk(Python_Expr_object(cls_name, l_dict), pos);
  }
  else {
    e = Python_Expr_mk(Python_Expr_const(value(st, obj)), pos);
  }

  if (!e)
    e = Python_Expr_mk(Python_Expr_const(Python_Const_none), pos);
  return e;
}

// Returns List Keyword
static lean_object* const_dict(struct state *st, PyObject *obj) {
  if (!obj) {
    error(st, "could not convert dictionary");
    return mkNil();
  }

  lean_object *arr = lean_mk_empty_array();
  lean_object *l_pos = curPos(st);

  Py_ssize_t pos = 0;
  PyObject *key, *val;
  while (PyDict_Next(obj, &pos, &key, &val)) {
    lean_object *s = py_strdup(st, key);
    lean_object *e = const_expr(st, val);
    arr = lean_array_push(arr, Python_Keyword_mk(mkOption(s), e, l_pos));
  }
  return lean_array_to_list(arr);
}

// returns List a
static lean_object* const_list(
       struct state *st, PyObject *obj,
       lean_object* (*f)(struct state*, PyObject*))
{
  if (!obj) return mkNil();

  Py_ssize_t sz = PyObject_Length(obj);
  if (sz <= 0) return mkNil();

  lean_object *arr = lean_alloc_array(0, sz);

  for (Py_ssize_t i = 0; i < sz; i++) {
    PyObject *key = PyLong_FromLong(i);
    if (!key) {
      error(st, "could not construct Long Object for key %ld", i);
      break;
    }

    // Note: Object_GetItem increments reference count
    PyObject *item = PyObject_GetItem(obj, key);
    Py_DECREF(key);
    if (!item) {
      error(st, "cound not get sequence item number %ld", i);
      break;
    }

    lean_object *e = f(st, item);
    Py_DECREF(item);
    if (e)
      arr = lean_array_push(arr, e);
  }
  return lean_array_to_list(arr);
}


// Note: in case of errors we will return an empty list (NULL)
// returns List Const
static lean_object* const_exprs(struct state *st, PyObject *obj) {
  return const_list(st, obj, const_expr);
}

// returns Nat
static lean_object* const_nat(struct state *st, PyObject *obj) {
  unsigned res = 0;
  if (!PyLong_Check(obj)) {
    error(st, "expecting a positive integer");
  } else {
    long val = PyLong_AsLong(obj);
    if (val < 0 || val > INT_MAX) {
      error(st, "expecting a positive integer, got %ld", val);
    } else {
      res = (unsigned)val;
    }
  }
  return lean_unsigned_to_nat(res);
}

// returns List Nat
static lean_object* nat_list(struct state *st, PyObject *obj) {
  return const_list(st, obj, const_nat);
}

// Add a new local variable to the current scope

static void add_local(struct state *st, lean_object *name) {
  struct local *l = region_alloc(st->region, sizeof(*l));
  l->next = st->scope.locals;
  l->name = lean_string_cstr(name);
  st->scope.locals = l;
}

// Try to add a new global reference to the environment. Note, this is
// best-effort as we are not completely sure that we need the global (or even
// if this really is a global reference) at this point. Later passes will raise
// more intelligent errors, so we can simply fail to add the reference.
// See: KLR/Trace/Python.lean for more details.

static void add_global(struct state *st, lean_object *name, PyObject *obj) {
  if (!name || !obj || have_def(st, lean_string_cstr(name)))
    return;

  struct definition *def = region_alloc(st->region, sizeof(*def));
  lean_object *pos = curPos(st);

  def->str = name;
  def->name = lean_string_cstr(name);
  def->type = GLOBAL;

  lean_object *c = const_expr(st, obj);
  def->obj = Python_Keyword_mk(mkSome(def->str), c, pos);

  def->next = st->defs;
  st->defs = def;
}

// Lookup item `id` in dictionary `name` which should be an attribute of `obj`.
// e.g. f.name['id']
static PyObject* lookup_(PyObject *obj, const char *name, PyObject *id) {
  if (!obj || !name || !id)
    return NULL;

  PyObject *dict = PyObject_GetAttrString(obj, name);
  if (!dict) return NULL;

  PyObject *value = PyDict_GetItem(dict, id);
  Py_DECREF(dict);

  if (value)
    Py_INCREF(value);
  return value;
}

// Lookup `id` in current environment
static PyObject* lookup(struct state *st, PyObject *id) {
  if (!st->scope.f || !id)
    return NULL;
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
  lean_object *name;  // String
  PyObject *obj;
};

static struct ref reference(struct state *st, struct _expr *e) {
  struct ref ref = { NULL, NULL };
  if (!e) return ref;

  switch(e->kind) {
  case Name_kind:
    ref.obj = lookup(st, e->v.Name.id);
    if (ref.obj) {
      if (PyModule_Check(ref.obj)) {
        PyObject *name = PyModule_GetNameObject(ref.obj);
        ref.name = py_strdup(st, name);
        Py_XDECREF(name);
      } else {
        ref.name = py_strdup(st, e->v.Name.id);
      }
    }
    break;

  case Attribute_kind:
    ref = reference(st, e->v.Attribute.value);
    if (!ref.obj) {
      ref.name = NULL;
      break;
    }

    if (PyObject_HasAttr(ref.obj, e->v.Attribute.attr)) {
      ref.obj = PyObject_GetAttr(ref.obj, e->v.Attribute.attr);
      ref.name = path_append(st, ref.name, e->v.Attribute.attr);
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
    if (PyFunction_Check(ref.obj) || PyType_Check(ref.obj)) {
      lean_dec(ref.name);
      ref.name = py_def_name(st, ref.obj);
      if (!st->ignore_refs)
        add_work(st, ref.obj);
    } else {
      if (!st->ignore_refs)
        add_global(st, ref.name, ref.obj);
    }
  }
  return ref;
}

// -----------------------------------------------------------------------------
// -- Constants

// The Python AST stores constants as Python objects in the heap.
// TODO: We are restricting int and float types very early, which is different
// from how the Lean code works.

// returns Const
static lean_object* value(struct state *st, PyObject *obj) {
  lean_object *c = Python_Const_none;

  if (!st || !obj || Py_IsNone(obj)) {
    // can use default value of c
  }
  else if (PyBool_Check(obj)) {
    c = Python_Const_bool(Py_IsTrue(obj) != 0);
  }
  else if (PyLong_Check(obj)) {
    int overflow = 0;
    PyErr_Clear();
    long value = PyLong_AsLongAndOverflow(obj, &overflow);
    if (value == -1 && PyErr_Occurred()) {
      PyErr_Clear();
      error(st, "could not convert integer value");
    }
    if (overflow < 0 || value < INT_MIN) {
      error(st, "integer value (%ld) is too small", value);
    }
    if (overflow > 0 || value > INT_MAX) {
      error(st, "integer value (%ld) is too large", value);
    } else {
      c = Python_Const_int(lean_int_to_int((int)value));
    }
  }
  else if (PyFloat_Check(obj)) {
    PyErr_Clear();
    double d = PyFloat_AsDouble(obj);
    if (PyErr_Occurred()) {
      PyErr_Clear();
      error(st, "could not convert float value");
    } else {
      c = Python_Const_float(d);
    }
  }
  else if (PyUnicode_Check(obj)) {
    c = Python_Const_string(py_strdup(st, obj));
  }
  else if (Py_IS_TYPE(obj, &PyEllipsis_Type)) {
    c = Python_Const_ellipsis;
  }
  return c;
}

// -----------------------------------------------------------------------------
// -- Expressions

static u8 context(expr_context_ty ctx) {
  switch (ctx) {
  case Load:  return Python_Ctx_load;
  case Store: return Python_Ctx_store;
  case Del:   return Python_Ctx_del;
  default:    return Python_Ctx_load;  // impossible (safe default)
  }
}

static u8 boolop(boolop_ty op) {
  switch (op) {
  case And: return Python_BoolOp_land;
  case Or:  return Python_BoolOp_lor;
  default:  return 0; // impossible
  }
}

static u8 unaryop(unaryop_ty op) {
  switch (op) {
  case Invert: return Python_UnaryOp_invert;
  case Not:    return Python_UnaryOp_not;
  case UAdd:   return Python_UnaryOp_uadd;
  case USub:   return Python_UnaryOp_usub;
  default:     return 0; // impossible
  }
}

static u8 binop(operator_ty op) {
  switch (op) {
  case Add:      return Python_BinOp_add;
  case Sub:      return Python_BinOp_sub;
  case Mult:     return Python_BinOp_mul;
  case MatMult:  return Python_BinOp_matmul;
  case Div:      return Python_BinOp_div;
  case Mod:      return Python_BinOp_mod;
  case Pow:      return Python_BinOp_pow;
  case LShift:   return Python_BinOp_lshift;
  case RShift:   return Python_BinOp_rshift;
  case BitOr:    return Python_BinOp_or;
  case BitXor:   return Python_BinOp_xor;
  case BitAnd:   return Python_BinOp_and;
  case FloorDiv: return Python_BinOp_floor;
  default:       return 0;  // impossible
  }
}

static u8 cmpop(cmpop_ty op) {
  switch (op) {
  case Eq:    return Python_CmpOp_eq;
  case NotEq: return Python_CmpOp_ne;
  case Lt:    return Python_CmpOp_lt;
  case LtE:   return Python_CmpOp_le;
  case Gt:    return Python_CmpOp_gt;
  case GtE:   return Python_CmpOp_ge;
  case Is:    return Python_CmpOp_is;
  case IsNot: return Python_CmpOp_isNot;
  case In:    return Python_CmpOp_isIn;
  case NotIn: return Python_CmpOp_notIn;
  default:    return 0; // impossible
  }
}

static lean_object* cmpops(struct state *st, asdl_int_seq *ops) {
  if (!ops)
    return mkNil();

  lean_object *arr = lean_alloc_array(0, ops->size);
  for (int i = 0; i < ops->size; i++) {
    u8 op = cmpop(ops->typed_elements[i]);
    arr = lean_array_push(arr, lean_box(op));
  }
  return lean_array_to_list(arr);
}

static lean_object* exprs(struct state *st, asdl_expr_seq *python);
static lean_object* keywords(struct state *st, asdl_keyword_seq *python);

static lean_object* expr(struct state *st, struct _expr *python) {
  struct pos old_pos = st->scope.pos;
  lean_object *e = NULL;

  if (!python)
    goto done;

  st->scope.pos.line = python->lineno;
  st->scope.pos.col = python->col_offset;

  //static int indent = 0;
  //indent++;
  //for (int i = 0; i < indent; i++) printf(" ");
  //printf("EXPR %d %p (%d, %d)\n", python->kind, python, python->lineno, python->col_offset);
  switch (python->kind) {
    case Constant_kind: {
      e = Python_Expr_const(value(st, python->v.Constant.value));
      break;
    }
    // Names and attributes may be references which we need to track
    // We rely on the ctx value for a small optimization: we only need
    // to consider Loads
    case Name_kind: {
      lean_object *name = NULL;
      if (python->v.Name.ctx == Load) {
        struct ref r = reference(st, python);
        if (r.obj)
          name = r.name;
      }
      if (!name)
        name = py_strdup(st, python->v.Name.id);

      if (python->v.Name.ctx == Store) {
        add_local(st, name);
      }

      e = Python_Expr_name(name, context(python->v.Name.ctx));
      break;
    }

    case Attribute_kind: {
      e = Python_Expr_attr(expr(st, python->v.Attribute.value),
                           py_strdup(st, python->v.Attribute.attr),
                           context(python->v.Attribute.ctx));

      if (python->v.Attribute.ctx == Load)
        reference(st, python);
      break;
    }

    // Containers: Tuple and List and Dict
    case Tuple_kind: {
      e = Python_Expr_tuple(exprs(st, python->v.Tuple.elts),
                            context(python->v.Tuple.ctx));
      break;
    }
    case List_kind: {
      e = Python_Expr_list(exprs(st, python->v.List.elts),
                           context(python->v.List.ctx));
      break;
    }
    case Dict_kind: {
      e = Python_Expr_dict(exprs(st, python->v.Dict.keys),
                           exprs(st, python->v.Dict.values));
      break;
    }

    // Index expressions
    case Subscript_kind: {
      e = Python_Expr_subscript(expr(st, python->v.Subscript.value),
                                expr(st, python->v.Subscript.slice),
                                context(python->v.Subscript.ctx));
      break;
    }
    case Slice_kind: {
      lean_object *lower = python->v.Slice.lower ? expr(st, python->v.Slice.lower) : NULL;
      lean_object *upper = python->v.Slice.upper ? expr(st, python->v.Slice.upper) : NULL;
      lean_object *step = python->v.Slice.step ? expr(st, python->v.Slice.step) : NULL;
      e = Python_Expr_slice(mkOption(lower),
                            mkOption(upper),
                            mkOption(step));
      break;
    }

    // Operators
    case BoolOp_kind: {
      e = Python_Expr_boolOp(boolop(python->v.BoolOp.op),
                             exprs(st, python->v.BoolOp.values));
      break;
    }
    case BinOp_kind: {
      e = Python_Expr_binOp(binop(python->v.BinOp.op),
                            expr(st, python->v.BinOp.left),
                            expr(st, python->v.BinOp.right));
      break;
    }
    case UnaryOp_kind: {
      e = Python_Expr_unaryOp(unaryop(python->v.UnaryOp.op),
                              expr(st, python->v.UnaryOp.operand));
      break;
    }
    case Compare_kind: {
      e = Python_Expr_compare(expr(st, python->v.Compare.left),
                              cmpops(st, python->v.Compare.ops),
                              exprs(st, python->v.Compare.comparators));
      break;
    }

    // Condition expression
    case IfExp_kind: {
      e = Python_Expr_ifExp(expr(st, python->v.IfExp.test),
                            expr(st, python->v.IfExp.body),
                            expr(st, python->v.IfExp.orelse));
      break;
    }

    // Function calls
    case Call_kind: {
      e = Python_Expr_call(expr(st, python->v.Call.func),
                           exprs(st, python->v.Call.args),
                           keywords(st, python->v.Call.keywords));
      break;
    }

    // Tuple expansion *t
    case Starred_kind: {
      e = Python_Expr_starred(expr(st, python->v.Starred.value),
                              context(python->v.Starred.ctx));
      break;
    }

    // f-strings
    case FormattedValue_kind: {
      if (python->v.FormattedValue.format_spec) {
        error(st, "NKI does no support format specifiers");
        break;
      }

      int conv = python->v.FormattedValue.conversion;
      lean_object *l_conv =
        conv <= 0 ? mkNone() : mkOption(lean_unsigned_to_nat(conv));

      lean_object *value_expr = python->v.FormattedValue.value ? expr(st, python->v.FormattedValue.value) : NULL;
      if (!value_expr) {
        error(st, "FormattedValue missing value");
        break;
      }
      e = Python_Expr_format(value_expr, l_conv);
      break;
    }
    case JoinedStr_kind: {
      e = Python_Expr_joined(exprs(st, python->v.JoinedStr.values));
      break;
    }

    default:
      error(st, "unsupported expression");
      break;
  }

done:
  checkPyErr(st);
  if (!e)
    e = Python_Expr_const(Python_Const_none);

  //for (int i = 0; i < indent; i++) printf(" ");
  //printf("expr %d %p\n", python->kind, python);
  //indent--;
  st->scope.pos = old_pos;
  return Python_Expr_mk(e, Pos(python));
}

// return List Expr
static lean_object *exprs(struct state *st, asdl_expr_seq *python) {
  if (!python)
    return mkNil();

  lean_object *arr = lean_alloc_array(0, python->size);
  for (int i = 0; i < python->size; i++) {
    lean_object *e = expr(st, python->typed_elements[i]);
    arr = lean_array_push(arr, e);
  }
  return lean_array_to_list(arr);
}

// -----------------------------------------------------------------------------
// -- Keywords

static lean_object* keyword(struct state *st, keyword_ty python) {
  // NULL means **kwarg
  lean_object *id = NULL;
  if (python->arg)
    id = py_strdup(st, python->arg);

  return Python_Keyword_mk(mkOption(id),
                           expr(st, python->value),
                           Pos(python));
}

static lean_object* keywords(struct state *st, asdl_keyword_seq *python) {
  if (!python)
    return mkNil();

  lean_object *arr = lean_alloc_array(0, python->size);
  for (int i = 0; i < python->size; i++) {
    lean_object *kw = keyword(st, python->typed_elements[i]);
    arr = lean_array_push(arr, kw);
  }
  return lean_array_to_list(arr);
}

// -----------------------------------------------------------------------------
// -- Arguments

static lean_object* arg(struct state *st, arg_ty python) {
  // NULL just means missing
  if (!python)
    return NULL;

  lean_object *name = py_strdup(st, python->arg);
  add_local(st, name);
  return name;
}

static lean_object* arg_list(struct state *st, asdl_arg_seq *python) {
  if (!python)
    return mkNil();

  lean_object *arr = lean_alloc_array(0, python->size);
  for (int i = 0; i < python->size; i++) {
    lean_object *str = arg(st, python->typed_elements[i]);
    if (!str) {
      error(st, "invalid argument name (null)");
    } else {
      arr = lean_array_push(arr, str);
    }
  }
  return lean_array_to_list(arr);
}

static lean_object* args(struct state *st, arguments_ty python) {
  if (!python)
    return NULL;

  // Note: process expressions last to avoid clearing errors
  lean_object *posonlyargs = arg_list(st, python->posonlyargs);
  lean_object *args = arg_list(st, python->args);
  lean_object *vararg = mkOption(arg(st, python->vararg));
  lean_object *kwonlyargs = arg_list(st, python->kwonlyargs);
  lean_object *kwarg = mkOption(arg(st, python->kwarg));

  lean_object *defaults = exprs(st, python->defaults);

  // TODO: this is a bug
  // The old version of gather computed the names of keyword defaults,
  // but this is not what the parser does.
  //as->kw_defaults = exprs(st, python->kw_defaults);
  lean_object *kw_defaults = mkNil();

  return Python_Args_mk(posonlyargs, args, defaults, vararg,
                        kwonlyargs, kw_defaults, kwarg);
}

// -----------------------------------------------------------------------------
// -- Statements

static lean_object* stmts(struct state *st, asdl_stmt_seq *python);

static lean_object* stmt(struct state *st, struct _stmt *python) {
  struct pos old_pos = st->scope.pos;
  lean_object *s = Python_Stmt_pass;

  if (!python)
    goto done;

  st->scope.pos.line = python->lineno;
  st->scope.pos.col = python->col_offset;

  //printf("STMT %d %p\n", python->kind, python);
  switch (python->kind) {
    case Pass_kind:
      s = Python_Stmt_pass;
      break;

    // Simple expressions
    case Expr_kind: {
      s = Python_Stmt_expr(expr(st, python->v.Return.value));
      break;
    }
    case Assert_kind: {
      // TODO capture message
      s = Python_Stmt_assert(expr(st, python->v.Assert.test));
      break;
    }
    case Return_kind: {
      s = Python_Stmt_ret(expr(st, python->v.Return.value));
      break;
    }

    // Assignments
    case Assign_kind: {
      s = Python_Stmt_assign(exprs(st, python->v.Assign.targets),
                             expr(st, python->v.Assign.value));
      break;
    }
    case AugAssign_kind: {
      s = Python_Stmt_augAssign(expr(st, python->v.AugAssign.target),
                                binop(python->v.AugAssign.op),
                                expr(st, python->v.AugAssign.value));
      break;
    }
    case AnnAssign_kind: {
      lean_object *value = mkNone();
      if (python->v.AnnAssign.value)
        value = mkSome(expr(st, python->v.AnnAssign.value));

      s = Python_Stmt_annAssign(expr(st, python->v.AnnAssign.target),
                                expr(st, python->v.AnnAssign.annotation),
                                value);
      break;
    }

    // If statements
    case If_kind: {
      s = Python_Stmt_ifStm(expr(st, python->v.If.test),
                            stmts(st, python->v.If.body),
                            stmts(st, python->v.If.orelse));
      break;
    }

    // For loops
    case For_kind: {
      s = Python_Stmt_forLoop(expr(st, python->v.For.target),
                              expr(st, python->v.For.iter),
                              stmts(st, python->v.For.body),
                              stmts(st, python->v.For.orelse));
      break;
    }
    case Break_kind: {
      s = Python_Stmt_breakLoop;
      break;
    }
    case Continue_kind: {
      s = Python_Stmt_continueLoop;
      break;
    }

    case While_kind: {
      s = Python_Stmt_whileLoop(expr(st, python->v.While.test),
                                stmts(st, python->v.While.body),
                                stmts(st, python->v.While.orelse));
      break;
    }

    // TODO: do we need with?
    case With_kind:
      error(st, "NKI does not support 'with' statements at this time.");
      break;

    case FunctionDef_kind:
      error(st, "NKI does not support inner function definitions. Move function definition outside this function.");
      break;

    case ClassDef_kind:
      error(st, "NKI does not support 'class' definitions within a function. Move class definition outside this function.");
      break;

    case Delete_kind:
      error(st, "NKI does not support 'del' statements at this time.");
      break;

    case TypeAlias_kind:
      error(st, "NKI does not support 'type' statements at this time.");
      break;

    case AsyncFunctionDef_kind:
    case AsyncFor_kind:
    case AsyncWith_kind:
      error(st, "NKI does not support 'async'. Use only synchronous functions within kernels.");
      break;

    case Match_kind:
      error(st, "NKI does not support 'match' statements at this time. Use 'if/elif' or dict lookups instead.");
      break;

    case Raise_kind:
      error(st, "NKI does not support 'raise' statements. Use 'if/else' control flow within kernels, or 'assert' for fatal errors.");
      break;

    case Try_kind:
    case TryStar_kind:
      error(st, "NKI does not support 'try' statements. Use 'if/else' control flow within kernels.");
      break;

    case Import_kind:
    case ImportFrom_kind:
      error(st, "NKI does not support 'import' statements within a function. Move 'import' outside this function.");
      break;

    case Global_kind:
      error(st, "NKI does not support 'global' statements. Kernels cannot assign to global variables. Pass a dict between functions to share state.");
      break;

    case Nonlocal_kind:
      error(st, "NKI does not support 'nonlocal' statements. Kernels cannot assign to variables in nonlocal scope. Pass a dict between functions to share state.");
      break;

    default:
      error(st, "This statement is not supported in NKI.");
      break;
  }

done:
  checkPyErr(st);
  //printf("stmt %d %p\n", python->kind, python);
  st->scope.pos = old_pos;
  return Python_Stmt_mk(s, Pos(python));
}

static lean_object* stmts(struct state *st, asdl_stmt_seq *python) {
  if (!python)
    return mkNil();

  lean_object *arr = lean_alloc_array(0, python->size);
  for (int i = 0; i < python->size; i++) {
    lean_object *s = stmt(st, python->typed_elements[i]);
    arr = lean_array_push(arr, s);
  }
  return lean_array_to_list(arr);
}

// -----------------------------------------------------------------------------
// -- Interface to the parser

static PyObject* get_util(const char *name) {
  PyObject *f = NULL;
  PyObject *fe = PyUnicode_FromString(MODULE_ROOT ".frontend");
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

static struct _mod* parse_def(struct state *st, PyObject *obj) {
  // Initialization needed for done label
  struct _mod *m = NULL;
  PyObject *source = NULL;

  PyObject *getsrc = get_util("_get_src");
  PyObject *args = PyTuple_Pack(1, obj);
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

  const char *file_str = PyUnicode_AsUTF8(file);
  const char *src_str = PyUnicode_AsUTF8(src);
  if (!file_str || !src_str)
    goto done;

  m = parse_string(src_str, file);
  if (m) {
    // everything checks out, enter new scope
    if (PyType_Check(obj)) {
      st->scope.cls = obj;
      st->scope.f = NULL;
    } else if (PyFunction_Check(obj)) {
      st->scope.cls = NULL;
      st->scope.f = obj;
    }
    st->scope.src = lean_mk_string(src_str);
    st->scope.file = lean_mk_string(file_str);
    st->scope.line_offset = PyLong_AsLong(line);
    st->scope.pos.line = 0;
    st->scope.pos.col = 0;
    st->scope.locals = NULL;
  }

done:
  Py_XDECREF(getsrc);
  Py_XDECREF(args);
  Py_XDECREF(source);
  return m;
}

static lean_object* function_(struct state *st, lean_object *name, struct _stmt *s) {
  // dont follow decorators
  st->ignore_refs = true;
  lean_object *decs = exprs(st, s->v.FunctionDef.decorator_list);
  st->ignore_refs = false;

  // process args first to register local names
  lean_object *as = args(st, s->v.FunctionDef.args);
  lean_object *body = stmts(st, s->v.FunctionDef.body);

  return Python_Fun_mk(name, st->scope.file,
                       lean_unsigned_to_nat(st->scope.line_offset),
                       st->scope.src, decs, as, body);
}

static void function(struct state *st, lean_object *name, struct _stmt *s) {
  lean_object *f = function_(st, name, s);

  struct definition *def = region_alloc(st->region, sizeof(*def));
  def->str = name;
  def->name = lean_string_cstr(name);
  def->type = FUN;
  def->obj = f;

  def->next = st->defs;
  st->defs = def;
}

// Returns Keyword
static lean_object* field(struct state *st, struct _expr *e) {
  if (e->kind != Name_kind) {
    error(st, "invalid left-hand side in assignment");
    return NULL;
  }

  PyObject *id = e->v.Name.id;
  lean_object *name = id ? mkSome(py_strdup(st, id)) : mkNone();
  lean_object *pos = Pos(e);
  lean_object *val = NULL;

  PyObject *obj = PyObject_GetAttr(st->scope.cls, e->v.Name.id);
  if (obj) {
    val = const_expr(st, obj);
    Py_DECREF(obj);
  } else {
    val = Python_Expr_mk(Python_Expr_const(Python_Const_none), pos);
  }

  return Python_Keyword_mk(name, val, pos);
}


static void class(struct state *st, lean_object *name, struct _stmt *s) {
  if (s->v.ClassDef.keywords &&
      s->v.ClassDef.keywords->size > 0)
  {
    error(st, "class keywords are not supported in NKI");
    return;
  }

  if (s->v.ClassDef.type_params &&
      s->v.ClassDef.type_params->size > 0)
  {
    error(st, "class type parameters are not supported in NKI");
    return;
  }

  // Check that class inherits from allowed base classes
  if (s->v.ClassDef.bases && s->v.ClassDef.bases->size > 0) {
    bool valid_base = true;
    for (int i = 0; i < s->v.ClassDef.bases->size; i++) {
      struct _expr *base = s->v.ClassDef.bases->typed_elements[i];
      const char *base_name = NULL;
      if (base->kind == Name_kind) {
        base_name = PyUnicode_AsUTF8(base->v.Name.id);
      } else if (base->kind == Attribute_kind) {
        // ignore module name (conservative)
        base_name = PyUnicode_AsUTF8(base->v.Attribute.attr);
      }
      if (base_name) {
        if (!strstr(base_name, "NKIObject") &&
            !strstr(base_name, "Enum"))
        {
          valid_base = false;
          break;
        }
      }
    }
    if (!valid_base) {
      error(st, "NKI classes must inherit from either Enum or NKIObject");
      return;
    }
  } else {
    // Not inheriting from any base is also a failure since there are
    // a good number of classes that are plain but are not valid in NKI
    error(st, "NKI classes must inherit from either Enum or NKIObject");
    return;
  }

  // don't follow base classes or decorators
  st->ignore_refs = true;
  lean_object *bases = exprs(st, s->v.ClassDef.bases);
  lean_object *decs = exprs(st, s->v.ClassDef.decorator_list);
  st->ignore_refs = false;

  asdl_stmt_seq *python = s->v.ClassDef.body;
  lean_object *fields = lean_mk_empty_array();
  lean_object *methods = lean_mk_empty_array();

  for (int i = 0; i < python->size; i++) {
    struct _stmt *s = python->typed_elements[i];
    if (!s)
      break;

    st->scope.pos.line = s->lineno;
    st->scope.pos.col = s->col_offset;

    switch (s->kind) {
    case Pass_kind:
      break;

    case Expr_kind:
      // Skip docstrings (string literals)
      if (s->v.Expr.value->kind == Constant_kind)
        break;
      error(st, "Expression statements not supported in NKI classes");
      return;

    case Assign_kind: {
      if (s->v.Assign.targets == NULL ||
          s->v.Assign.targets->size != 1)
      {
        error(st, "invalid assignment in NKI class");
        return;
      }
      lean_object *f = field(st, s->v.Assign.targets->typed_elements[0]);
      fields = lean_array_push(fields, f);
      break;
    }
    case AnnAssign_kind: {
      lean_object *f = field(st, s->v.AnnAssign.target);
      fields = lean_array_push(fields, f);
      break;
    }
    case FunctionDef_kind: {
      PyObject *f = PyObject_GetAttr(st->scope.cls, s->v.FunctionDef.name);
      lean_object *m_name = py_method_name(st, name, f);

      // Note: we don't support nesting, so this is valid
      st->scope.f = f;
      lean_object *m = function_(st, m_name, s);
      st->scope.f = NULL;
      st->scope.locals = NULL;
      methods = lean_array_push(methods, m);
      break;
    }
    default:
      error(st, "Statement not supported in NKI classes");
      return;
    }
  }

  lean_object *cls = Python_Class_mk(
    name,
    bases,
    decs,
    lean_array_to_list(fields),
    lean_array_to_list(methods));

  struct definition *def = region_alloc(st->region, sizeof(*def));
  def->str = name;
  def->name = lean_string_cstr(name);
  def->type = CLS;
  def->obj = cls;

  def->next = st->defs;
  st->defs = def;
}

static void definition(struct state *st, PyObject *obj) {
  struct scope old_scope = st->scope;
  struct _mod *m = parse_def(st, obj);
  if (!m ||
      m->kind != Interactive_kind ||
      !m->v.Interactive.body ||
      m->v.Interactive.body->size != 1)
  {
    // failure to parse is not an error
    PyErr_Clear();
    goto cleanup;
  }

  struct _stmt *stmt = m->v.Interactive.body->typed_elements[0];
  st->scope.pos.line = stmt->lineno;
  st->scope.pos.col = stmt->col_offset;

  lean_object *name = py_def_name(st, obj);
  // add name to locals to prevent recursion
  add_local(st, name);

  switch (stmt->kind) {
  case FunctionDef_kind:
    if (st->scope.f)
      function(st, name, stmt);
    break;

  case ClassDef_kind:
    if (st->scope.cls)
      class(st, name, stmt);
    break;

  default:
    break;
  }

cleanup:
  if (m) free_python_ast(m);
  st->scope = old_scope;
}

// ----------------------------------------------------------------------------
// -- Entry points


static void append(PyObject **l, const char *r) {
  if (!l || !*l) return;
  if (!r) {
    *l = NULL;
    return;
  }
  PyObject *str = PyUnicode_FromString(r);
  if (!str) {
    *l = NULL;
    return;
  }
  PyUnicode_AppendAndDel(l, str);
}

PyObject* specialize(struct kernel *k, PyObject *args, PyObject *kws, PyObject *grid, PyObject *schedule) {
  struct state st = { 0 };
  st.region = k->region;

  // add main function to work list, and process arguments
  // potentially adding more dependencies to the work list
  add_work(&st, k->f);
  lean_object *l_args = args == Py_None ? mkNil() : const_exprs(&st, args);
  lean_object *l_kwargs = kws == Py_None ? mkNil() : const_dict(&st, kws);

  while (true) {
    struct worklist *work = st.work;
    if (!work) break;
    st.work = work->next;
    definition(&st, work->obj);
  }

  // Process additional kernel data from user
  // (ignoring any generated work items)
  long grid_val = 0;
  if (grid != Py_None) {
    grid_val = PyLong_AsLong(grid);
    if (grid_val < 0 || grid_val > 8)
      error(&st, "grid must be between 0 and 8");
  }
  lean_object *l_grid = lean_unsigned_to_nat((u32)grid_val);

  st.ignore_refs = true;
  lean_object *l_sched = schedule == Py_None ? mkNil() : const_exprs(&st, schedule);
  checkPyErr(&st);
  st.ignore_refs = false;
  st.work = NULL;

  // Build the kernel object
  lean_object *fs = lean_mk_empty_array();
  lean_object *cs = lean_mk_empty_array();
  lean_object *gs = lean_mk_empty_array();
  for (struct definition *d = st.defs; d; d = d->next) {
    switch (d->type) {
    case FUN: fs = lean_array_push(fs, d->obj); break;
    case CLS: cs = lean_array_push(cs, d->obj); break;
    case GLOBAL: gs = lean_array_push(gs, d->obj); break;
    }
  }

  lean_object *l_k = Python_Kernel_mk(
    py_def_name(&st, k->f),
    lean_array_to_list(fs),
    lean_array_to_list(cs),
    l_args,
    l_kwargs,
    lean_array_to_list(gs),
    l_grid,
    l_sched);

  // save the constructed kernel
  if (k->lean_kernel) {
    if (k->lean_kernel->kernel)
      lean_dec(k->lean_kernel->kernel);
  } else {
    k->lean_kernel = calloc(1, sizeof(struct lean_kernel));
  }
  k->lean_kernel->kernel = l_k;

  // convert warnings and errors to JSON string for Python
  char *buf;
  PyObject *json = PyUnicode_FromString("{\"warnings\":[");

  bool first = true;
  for (struct message *m = st.messages; m; m = m->next) {
    if (m->isError)
      continue;

    if (first) first = false;
    else append(&json, ",");

    if (asprintf(&buf, "\"%s:%d:%d %s\"", m->file, m->line, m->col, m->message) != -1) {
      append(&json, buf);
      free(buf);
    }
  }
  append(&json, "], \"errors\":[");

  first = true;
  for (struct message *m = st.messages; m; m = m->next) {
    if (!m->isError)
      continue;

    if (first) first = false;
    else append(&json, ",");

    if (asprintf(&buf, "\"%s:%d:%d %s\"", m->file, m->line, m->col, m->message) != -1) {
      append(&json, buf);
      free(buf);
    }
  }
  append(&json, "]}");
  return json;
}

lean_object* nki_to_json(lean_object*);

const char* serialize_python(struct kernel *k) {
  if (!k->lean_kernel) {
    specialize(k, Py_None, Py_None, Py_None, Py_None);
  }

  if (!k->lean_kernel) {
    PyErr_SetString(PyExc_RuntimeError, "No valid kernel in serialize");
    return NULL;
  }
  lean_inc(k->lean_kernel->kernel);
  lean_object *json = nki_to_json(k->lean_kernel->kernel);
  return lean_string_cstr(json);
}

lean_object* nki_trace(lean_object*, lean_object*, lean_object*, lean_object*);

// from util/io implemented in Init/System/IOError.lean
lean_object* lean_io_error_to_string(lean_object*);

const char* trace(struct kernel *k, const char *dst_file, const char* dst_format) {
  if (!k->lean_kernel) {
    PyErr_SetString(PyExc_RuntimeError, "No valid kernel to serialize");
    return NULL;
  }

  lean_object *file = lean_mk_string(dst_file);
  lean_object *format = lean_mk_string(dst_format);
  lean_object *world = lean_io_mk_world();
  lean_inc(k->lean_kernel->kernel);
  lean_object *res = nki_trace(k->lean_kernel->kernel, file, format, world);

  if (lean_io_result_is_ok(res)) {
    lean_object *str = lean_io_result_take_value(res);
    return lean_string_cstr(str);
  } else {
    lean_object *err = lean_io_result_get_error(res);
    lean_object *str = lean_io_error_to_string(err);
    PyErr_SetString(PyExc_RuntimeError, lean_string_cstr(str));
    lean_dec(str);
    return NULL;
  }
}
