/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include <list>
#include <stdarg.h>
#include <string>

#include "lean_ast.h"
#include "frontend.h"
#include "ast_python.h"
#include "refcount_ptr.hpp"

// Like std::shared_ptr/unique_ptr, but for lean_object*.
// Calls lean_dec() on destruction, if it still holds a pointer.
// When setting a pointer, it MUST be one that you own.
// BE CAREFUL: Lean APIs usually steal ownership of their function arguments.
// If a lean function takes `lean_object *` or `lean_obj_arg`, then you MUST
// pass ownership of the arg like: `lean_stealing_fn(my_lean_rc_ptr.release())`.
// If a lean function takes `b_lean_obj_arg`, then it is only borrowing the
// reference, and you call it like: `lean_borrowing_fn(my_lean_rc_ptr.get())`.
using lean_rc_ptr = refcount_ptr<lean_object, lean_inc, lean_dec>;

// Like shared_ptr/unique_ptr, but for PyObject*.
// If non-null, calls Py_DECREF() on destruction.
// When creating, you MUST pass in a reference that you own.
// DO NOT put a borrowed reference in here unless you Py_INCREF() first.
using python_rc_ptr = refcount_ptr<PyObject, Py_IncRef, Py_DecRef>;

// TODO: error handling treatise

/*
-- Gather
-- fetch all of the data we need from the Python environment

This code is almost entirely structural. The only interesting thing this code
does is in the handling of name and attribute expressions, where it will find
references to other code and recursively load the referenced code.
*/

struct lean_kernel {
  lean_rc_ptr entry;   // String
  lean_rc_ptr funs;    // List Fun
  lean_rc_ptr cls;     // List Cls
  lean_rc_ptr globals; // List Keyword
  lean_rc_ptr kernel;  // Kernel
};

struct state {
  // if true, do not follow references
  bool ignore_refs = false;

  // definitions to be processed
  struct work {
    const char *name() const { return lean_string_cstr(str.get()); }
    lean_rc_ptr str;  // this is the string "name"
    python_rc_ptr obj;
  };
  std::list<work> worklist; // using list (not vector) for simplicity, since we modify this while iterating it

  // Set of processed definitions
  struct definition {
    const char *name() const { return lean_string_cstr(str.get()); }
    lean_rc_ptr str; // this is the string "name"
    enum { FUN, CLS, GLOBAL } type;
    lean_rc_ptr obj; // type: Fun, Cls, or Keyword
  };
  std::list<definition> defs;

  // Current class/function scope
  struct scope_item {
    python_rc_ptr cls;    // python class we are working on
    python_rc_ptr f;      // python function we are working on
    lean_rc_ptr src;      // source code of definition
    lean_rc_ptr file;     // filename where definition lives
    u32 line_offset = 0;  // line number in `file` where definition lives
    u32 pad = 0;
    // Current AST node location
    struct pos {
      u32 line = 0, col = 0;
    } pos;
  } scope;
};

// Generate a (Python) syntax error at the current location
// During the gather phase we use the Python syntax error exception
// to report errors. In later phases we create our own error messages.
// Note: if we get an error while building the error, the user will get
// the error we got here, e.g. NoMemory, etc.

static void syntax_error(const struct state *st, const char *format, ...) {
  va_list vargs;
  va_start(vargs, format);
  PyErr_FormatV(PyExc_SyntaxError, format, vargs);
  va_end(vargs);

  if (st->scope.file) {
    PyErr_SyntaxLocationEx(lean_string_cstr(st->scope.file.get()),
        st->scope.line_offset + st->scope.pos.line - 1,
        st->scope.pos.col);
  }
}


// Return whether a definition with this name already exists.
// This function never raises exceptions.
static bool have_def(const struct state *st, const char *name) {
  for (const auto &d : st->defs) {
    if (strcmp(d.name(), name) == 0)
      return true;
  }
  return false;
}

// Create new Python string from Lean string.
// On failure, returns NULL with an exception set.
static PyObject* py_string_from_lean(lean_rc_ptr l_str) {
  return PyUnicode_FromStringAndSize(lean_string_cstr(l_str.get()), lean_string_len(l_str.get()));
}

// Copy a Python string to the Lean heap.
// On failure, returns NULL with an exception set.
static lean_rc_ptr py_strdup(PyObject *obj) {
  if (!obj) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  Py_ssize_t sz = -1;
  const char *s = PyUnicode_AsUTF8AndSize(obj, &sz);
  if (!s) {
    return NULL;
  }

  return lean_rc_ptr(lean_mk_string_from_bytes(s, sz));
}

// Create new Lean string, formatted like "{base}.{obj}".
// On failure, returns NULL with an exception set.
static lean_rc_ptr path_append(lean_rc_ptr base, PyObject *obj) {
  lean_rc_ptr lid = py_strdup(obj);
  if (!lid)
    return NULL;

  lean_object *base_dot = lean_string_append(base.release(), lean_mk_string("."));
  return lean_rc_ptr(lean_string_append(base_dot, lid.get()));
}

// Construct a path name from two Python strings, formatted like "{m}.{x}".
// On failure, returns NULL with an exception set.
static inline lean_rc_ptr py_path_name(PyObject *m, PyObject *x) {
  if (!m || !x) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }
  lean_rc_ptr base = py_strdup(m);
  if (!base)
    return NULL;

  return path_append(std::move(base), x);
}

// Construct full name of python function or class.
// On failure, returns NULL with an exception set.
static lean_rc_ptr py_def_name(PyObject *f) {
  auto module_ = python_rc_ptr(PyObject_GetAttrString(f, "__module__"));
  if (!module_)
    return NULL;

  auto name = python_rc_ptr(PyObject_GetAttrString(f, "__name__"));
  if (!name)
    return NULL;

  return py_path_name(module_.get(), name.get());
}

// Construct full name of python method
// On failure, returns NULL with an exception set.
static lean_rc_ptr py_method_name(lean_rc_ptr clsname, PyObject *f) {
  auto name = python_rc_ptr(PyObject_GetAttrString(f, "__name__"));
  if (!name)
    return NULL;

  return path_append(std::move(clsname), name.get());
}

// Add a new item to the work-list (if necessary)
// Note: we are clearing any possible errors from Python as this function
// is allowed to fail.
static void add_work(struct state *st, PyObject *obj) {
  lean_rc_ptr str = py_def_name(obj);
  if (!str)
    return;
  const char *name = lean_string_cstr(str.get());

  // skip numpy (for performance)
  if (strncmp("numpy.", name, 6) == 0) {
    return;
  }

  // skip enum (for correctness)
  if (strncmp("enum.", name, 5) == 0) {
    return;
  }

  if (have_def(st, name)) {
    return;
  }

  // skip if already in worklist
  for (const auto &work : st->worklist) {
    if (strcmp(work.name(), name) == 0) {
      return;
    }
  }

  // add to worklist
  state::work &new_work = st->worklist.emplace_back();
  new_work.str = std::move(str);
  Py_INCREF(obj);
  new_work.obj = python_rc_ptr(obj);
}

// -- functions for building basic types

// This function cannot fail.
static inline lean_rc_ptr mkNone() {
  return lean_rc_ptr(lean_box(0));
}

// This function cannot fail.
static lean_rc_ptr mkSome(lean_rc_ptr obj) {
  auto some = lean_rc_ptr(lean_alloc_ctor(1, 1, 0));
  lean_ctor_set(some.get(), 0, obj.release());
  return some;
}

// This function cannot fail.
static inline lean_rc_ptr mkOption(lean_rc_ptr obj) {
  return obj ? mkSome(std::move(obj)) : mkNone();
}

// This function cannot fail.
static inline lean_rc_ptr mkNil() {
  return lean_rc_ptr(lean_box(0));
}

// This function cannot fail.
static inline lean_rc_ptr
mkPos(unsigned line, unsigned column,
      unsigned lineEnd, unsigned columnEnd,
      lean_rc_ptr filename)
{
  return lean_rc_ptr(Core_Pos_mk(
    lean_unsigned_to_nat(line),
    lean_unsigned_to_nat(column),
    mkOption(lean_rc_ptr(lean_unsigned_to_nat(lineEnd))).release(),
    mkOption(lean_rc_ptr(lean_unsigned_to_nat(columnEnd))).release(),
    mkOption(std::move(filename)).release()));
}

// This function cannot fail.
#define Pos(obj) mkPos(obj->lineno, obj->end_lineno, \
                       obj->col_offset, obj->end_col_offset, st->scope.file)

static lean_rc_ptr value(struct state *st, PyObject *obj);
static lean_rc_ptr const_exprs(struct state *st, PyObject *obj);
static lean_rc_ptr nat_list(struct state *st, PyObject *obj);

// Check if object is a tensor type
// This function never raises exceptions.
static bool is_tensor(PyObject *obj) {
  PyTypeObject *t = Py_TYPE(obj);
  if (!t) return 0;

  return strcmp(t->tp_name, "tensor") == 0 ||         // nki
         strcmp(t->tp_name, "numpy.ndarray") == 0 ||  // numpy
         strcmp(t->tp_name, "Tensor") == 0 ||         // PyTorch
         strcmp(t->tp_name, "ShapedArray") == 0;      // JAX
}

// Handle tensor objects (return Const)
// On failure, returns NULL with an exception set.
static lean_rc_ptr tensor_const(struct state *st, PyObject *obj) {
  auto shape = python_rc_ptr(PyObject_GetAttrString(obj, "shape"));
  if (!shape) return NULL;

  lean_rc_ptr sh = nat_list(st, shape.get());
  if (!sh) return NULL;

  auto dtype = python_rc_ptr(PyObject_GetAttrString(obj, "dtype"));
  if (!dtype) return NULL;

  auto dstr = python_rc_ptr(PyObject_Str(dtype.get()));
  if (!dstr) return NULL;

  lean_rc_ptr dty = py_strdup(dstr.get());
  if (!dty) return NULL;

  return lean_rc_ptr(Python_Const_tensor(sh.release(), dty.release()));
}

// This function never raises exceptions
// Returns a new reference, or NULL
static python_rc_ptr get_numpy_generic_dtype() {
  // Try to get already imported numpy module
  auto numpy_name = python_rc_ptr(PyUnicode_FromString("numpy"));
  if (!numpy_name) {
    PyErr_Clear();
    return NULL;
  }

  auto numpy = python_rc_ptr(PyImport_GetModule(numpy_name.get()));
  if (!numpy) {
    PyErr_Clear();
    return NULL;
  }

  // Get numpy.generic class
  auto generic_class = python_rc_ptr(PyObject_GetAttrString(numpy.get(), "generic"));
  if (!generic_class) {
    PyErr_Clear();
    return NULL;
  }
  return generic_class;
}

// Check if object is numpy dtype
// This function never raises exceptions
static bool is_numpy_dtype(PyObject *obj) {
  python_rc_ptr generic_dtype = get_numpy_generic_dtype();
  if (!generic_dtype) return false;

  // Check if obj is instance of numpy.generic or subclass
  int result = PyObject_IsSubclass(obj, generic_dtype.get());
  return result == 1;
}

// Check if object is numpy dtype instance, if it is, then return dtype object.
// Otherwise return NULL
//
// This function never raises exceptions
static python_rc_ptr numpy_dtype_instance(PyObject *obj) {
  // NOTE: order matters here. If attemting to get type attr from
  // object before attempting to import numpy the object comes out
  // blank
  python_rc_ptr generic_dtype = get_numpy_generic_dtype();
  if (!generic_dtype) return NULL;

  auto obj_type = python_rc_ptr(PyObject_GetAttrString(obj, "type"));
  if (!obj_type) {
    PyErr_Clear();
    return NULL;
  }

  // Check if obj is instance of numpy.generic or subclass
  int result = PyObject_IsSubclass(obj_type.get(), generic_dtype.get());

  if (result == 1) { // it's -1 when it's false
    return obj_type;
  }

  return NULL;
}

// Return name of suggested type, or NULL.
// This function never raises exceptions.
static const char* suggest_nki_dtype(PyObject *obj) {
  const char* t = ((PyTypeObject*)obj)->tp_name;
  if (!t) return NULL;

  if (strstr(t, "numpy.uint8")) return "neuronxcc.nki.language.uint8";
  if (strstr(t, "numpy.int8")) return "neuronxcc.nki.language.int8";
  if (strstr(t, "numpy.uint16")) return "neuronxcc.nki.language.uint16";
  if (strstr(t, "numpy.int16")) return "neuronxcc.nki.language.int16";
  if (strstr(t, "numpy.uint32")) return "neuronxcc.nki.language.uint32";
  if (strstr(t, "numpy.int32")) return "neuronxcc.nki.language.int32";
  if (strstr(t, "numpy.float16")) return "neuronxcc.nki.language.float16";
  if (strstr(t, "numpy.float32")) return "neuronxcc.nki.language.float32";
  if (strstr(t, "numpy.bool")) return "neuronxcc.nki.language.bool";

  return NULL;
}

static lean_rc_ptr const_dict(struct state *st, PyObject *obj);

// returns Expr
// On failure, returns NULL with an exception set
static lean_rc_ptr const_expr(struct state *st, PyObject *obj) {
  lean_rc_ptr pos = mkPos(0, 0, 0, 0, st->scope.file);

  lean_rc_ptr c = value(st, obj);
  if (c) {
    return lean_rc_ptr(Python_Expr_mk(Python_Expr_const(c.release()), pos.release()));
  }

  // value may have set an exception, clear it
  PyErr_Clear();

  // Check for other types of supported global values
  if (PyTuple_Check(obj)) {
    lean_rc_ptr l = const_exprs(st, obj);
    if (!l) return NULL;
    return lean_rc_ptr(Python_Expr_mk(Python_Expr_tuple(l.release(), Python_Ctx_load), pos.release()));
  }
  else if (PyList_Check(obj)) {
    lean_rc_ptr l = const_exprs(st, obj);
    if (!l) return NULL;
    return lean_rc_ptr(Python_Expr_mk(Python_Expr_list(l.release(), Python_Ctx_load), pos.release()));
  }
  else if (PyDict_Check(obj)) {
    auto keys = python_rc_ptr(PyDict_Keys(obj));
    if (!keys) return NULL;

    auto vals = python_rc_ptr(PyDict_Values(obj));
    if (!vals) return NULL;

    lean_rc_ptr l_keys = const_exprs(st, keys.get());
    if (!l_keys) return NULL;

    lean_rc_ptr l_vals = const_exprs(st, vals.get());
    if (!l_vals) return NULL;

    return lean_rc_ptr(Python_Expr_mk(Python_Expr_dict(l_keys.release(), l_vals.release()), pos.release()));
  }
  else if (PyModule_Check(obj)) {
    const char *name = PyModule_GetName(obj);
    if (!name) {
      return NULL;
    }
    return lean_rc_ptr(Python_Expr_mk(Python_Expr_name(lean_mk_string(name), Python_Ctx_load), pos.release()));
  }
  else if (is_tensor(obj)) {
    lean_rc_ptr c = tensor_const(st, obj);
    if (!c) return NULL;
    return lean_rc_ptr(Python_Expr_mk(Python_Expr_const(c.release()), pos.release()));
  }
  else if (is_numpy_dtype(obj)) {
    const char* nki_dtype = suggest_nki_dtype(obj);
    if (nki_dtype) {
      syntax_error(st, "numpy dtypes are not supported as arguments. Use %s instead", nki_dtype);
    } else {
      syntax_error(st, "numpy dtypes are not supported as arguments");
    }
    return NULL;
  }
  else if (python_rc_ptr numpy_dt = numpy_dtype_instance(obj)) {
    const char* nki_dtype = suggest_nki_dtype(numpy_dt.get());
    if (nki_dtype) {
      syntax_error(st, "numpy dtypes are not supported as arguments. Use %s instead", nki_dtype);
    } else {
      syntax_error(st, "numpy dtypes are not supported as arguments");
    }
    return NULL;
  }
  else if (PyObject_HasAttrString(obj, "__class__") &&
           PyObject_HasAttrString(obj, "__dict__"))
  {
    // general object types
    auto cls = python_rc_ptr(PyObject_GetAttrString(obj, "__class__"));
    if (!cls) return NULL;

    auto dict = python_rc_ptr(PyObject_GetAttrString(obj, "__dict__"));
    if (!dict) return NULL;

    lean_rc_ptr cls_name = py_def_name(cls.get());
    if (!cls_name) return NULL;

    lean_rc_ptr l_dict = const_dict(st, dict.get());
    if (!l_dict) return NULL;

    add_work(st, cls.get());
    return lean_rc_ptr(Python_Expr_mk(Python_Expr_object(cls_name.release(), l_dict.release()), pos.release()));
  }

  syntax_error(st, "unsupported const expr type");
  return NULL;
}

// Returns List Keyword
// On failure, returns NULL with an exception set
static lean_rc_ptr const_dict(struct state *st, PyObject *obj) {
  auto arr = lean_rc_ptr(lean_mk_empty_array());
  lean_rc_ptr l_pos = mkPos(st->scope.pos.line,
                              st->scope.pos.col,
                              0, 0, st->scope.file);

  Py_ssize_t pos = 0;
  PyObject *key, *val; // PyDict_Next() will set these to borrowed references
  while (PyDict_Next(obj, &pos, &key, &val)) {
    lean_rc_ptr s = py_strdup(key);
    if (!s) return NULL;

    lean_rc_ptr e = const_expr(st, val);
    if (!e) {
      if (!PyErr_Occurred()) {
        PyErr_Format(PyExc_ValueError, "%S is not a supported NKI type.", val);
      }
      return NULL;
    }

    lean_rc_ptr l_pos_incref = l_pos;
    lean_object *keyword = Python_Keyword_mk(mkOption(std::move(s)).release(), e.release(), l_pos_incref.release());
    arr = lean_rc_ptr((lean_array_push(arr.release(), keyword)));
  }
  return lean_rc_ptr(lean_array_to_list(arr.release()));
}

// returns List
// On failure, returns NULL with an exception set
static lean_rc_ptr const_list(
       struct state *st, PyObject *obj,
       lean_rc_ptr (*f)(struct state*, PyObject*))
{
  if (!obj) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  Py_ssize_t sz = PyObject_Length(obj);
  if (sz == -1) return NULL;

  auto arr = lean_rc_ptr(lean_alloc_array(0, sz));

  for (Py_ssize_t i = 0; i < sz; i++) {
    auto key = python_rc_ptr(PyLong_FromLong(i));
    if (!key) return NULL;

    // Note: Object_GetItem increments reference count
    auto item = python_rc_ptr(PyObject_GetItem(obj, key.get()));
    if (!item) return NULL;

    lean_rc_ptr e = f(st, item.get());
    if (!e) {
      if (!PyErr_Occurred()) {
        PyErr_Format(PyExc_ValueError, "%S is not a supported NKI type", item.get());
      }
      return NULL;
    }
    arr = lean_rc_ptr(lean_array_push(arr.release(), e.release()));
  }
  return lean_rc_ptr(lean_array_to_list(arr.release()));
}


// returns List Const
// On failure, returns NULL with an exception set
static lean_rc_ptr const_exprs(struct state *st, PyObject *obj) {
  return const_list(st, obj, const_expr);
}

// returns Const Nat
// On failure, returns NULL with an exception set
static lean_rc_ptr const_nat(struct state *st, PyObject *obj) {
  if (!PyLong_Check(obj)) {
    syntax_error(st, "expecting a positive integer");
    return NULL;
  }

  long val = PyLong_AsLong(obj);
  if (val < 0 || val > INT_MAX) {
    syntax_error(st, "expecting a positive integer");
    return NULL;
  }

  return lean_rc_ptr(lean_unsigned_to_nat((unsigned)val));
}

// returns List Nat
// On failure, returns NULL with an exception set
static lean_rc_ptr nat_list(struct state *st, PyObject *obj) {
  return const_list(st, obj, const_nat);
}

// Try to add a new global reference to the environment. Note, this is
// best-effort as we are not completely sure that we need the global (or even
// if this really is a global reference) at this point. Later passes will raise
// more intelligent errors, so we can simply fail to add the reference.
// See: KLR/Trace/Python.lean for more details.

static void add_global(struct state *st, lean_rc_ptr name, PyObject *obj) {
  if (!name || !obj || have_def(st, lean_string_cstr(name.get())))
    return;

  lean_rc_ptr c = const_expr(st, obj);
  if (!c) {
    PyErr_Clear();
    return;
  }

  state::definition &def = st->defs.emplace_back();
  lean_rc_ptr pos = mkPos(0, 0, 0, 0, st->scope.file);

  def.str = std::move(name);
  def.type = state::definition::GLOBAL;
  def.obj = lean_rc_ptr(Python_Keyword_mk(mkSome(def.str).release(), c.release(), pos.release()));
}

// Lookup item `id` in dictionary `name` which should be an attribute of `obj`.
// e.g. f.name['id']
// No exception is ever set, since it's OK for lookup to fail.
static python_rc_ptr lookup_(PyObject *obj, const char *name, PyObject *id) {
  if (!obj || !name || !id)
    return NULL;

  // PyObject_GetAttrString() returns new reference, or sets exception
  auto dict  = python_rc_ptr(PyObject_GetAttrString(obj, name));
  if (!dict) {
    PyErr_Clear();
    return NULL;
  }

  // PyDict_GetItem() returns borrowed reference, and never sets exceptions
  PyObject *value = PyDict_GetItem(dict.get(), id);
  if (!value) return NULL;

  Py_INCREF(value);
  return python_rc_ptr(value);
}

// Lookup `id` in current environment
// No exception is ever set, since it's OK for lookup to fail.
static python_rc_ptr lookup(struct state *st, PyObject *id) {
  if (!st->scope.f)
    return NULL;
  python_rc_ptr global = lookup_(st->scope.f.get(), "__globals__", id);
  if (global)
    return global;

  return lookup_(st->scope.f.get(), "__builtins__", id);
}

// Record reference to expression `e`, which is either a name or an attribute,
// which we can think of as a pathname. For each element of the pathname, we
// lookup the name in the Python environment and either: add the value to our
// globals, or, if it is a function, add the function to our work list.

struct ref {
  lean_rc_ptr name;  // String
  python_rc_ptr obj;
};

// If reference found, returns ref.obj containing new reference.
// If not found, ref.obj will be NULL.
// No exception is ever set, it's OK if we fail to record a reference,
// later passes will raise more intelligent errors.
static struct ref reference(struct state *st, struct _expr *e) {
  struct ref ref;
  if (!e) return ref;

  switch(e->kind) {
  case Name_kind:
    ref.obj = lookup(st, e->v.Name.id);
    if (ref.obj)
      ref.name = py_strdup(e->v.Name.id);
    break;

  case Attribute_kind: {
    struct ref attr_value_ref = reference(st, e->v.Attribute.value);
    if (!attr_value_ref.obj) {
      break;
    }

    if (PyObject_HasAttr(attr_value_ref.obj.get(), e->v.Attribute.attr)) {
      ref.obj = python_rc_ptr(PyObject_GetAttr(attr_value_ref.obj.get(), e->v.Attribute.attr));
      ref.name = path_append(std::move(attr_value_ref.name), e->v.Attribute.attr);
    }
    break;
  }

  default:
    break;
  }

  if (ref.name && ref.obj) {
    if (PyFunction_Check(ref.obj.get()) || PyType_Check(ref.obj.get())) {
      ref.name = py_def_name(ref.obj.get());
      if (!st->ignore_refs)
        add_work(st, ref.obj.get());
    } else {
      if (!st->ignore_refs)
        add_global(st, ref.name, ref.obj.get());
    }
  } else {
    ref.obj.reset();
    ref.name.reset();
  }
  PyErr_Clear(); // Make sure we don't report any errors
  return ref;
}

// -----------------------------------------------------------------------------
// -- Constants

// The Python AST stores constants as Python objects in the heap.
// TODO: We are restricting int and float types very early, which is different
// from how the Lean code works.

// returns Const
// On failure, returns NULL with an exception set.
static lean_rc_ptr value(struct state *st, PyObject *obj) {
  if (!st || !obj) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  if (Py_IsNone(obj)) {
    lean_inc(Python_Const_none);
    return lean_rc_ptr(Python_Const_none);
  }
  else if (PyBool_Check(obj)) {
    return lean_rc_ptr(Python_Const_bool(Py_IsTrue(obj) != 0));
  }
  else if (PyLong_Check(obj)) {
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
    return lean_rc_ptr(Python_Const_int(lean_int_to_int((int)value)));
  }
  else if (PyFloat_Check(obj)) {
    double d = PyFloat_AsDouble(obj);
    if (PyErr_Occurred())
      return NULL;
    return lean_rc_ptr(Python_Const_float(d));
  }
  else if (PyUnicode_Check(obj)) {
    lean_rc_ptr str = py_strdup(obj);
    if (!str)
      return NULL;
    return lean_rc_ptr(Python_Const_string(str.release()));
  }
  else if (Py_IS_TYPE(obj, &PyEllipsis_Type)) {
    lean_inc(Python_Const_ellipsis);
    return lean_rc_ptr(Python_Const_ellipsis);
  }
  else {
    syntax_error(st, "unsupported value type");
    return NULL;
  }
}

// -----------------------------------------------------------------------------
// -- Expressions

// This function never raises exceptions.
static u8 context(expr_context_ty ctx) {
  switch (ctx) {
  case Load:  return Python_Ctx_load;
  case Store: return Python_Ctx_store;
  case Del:   return Python_Ctx_del;
  default:    return Python_Ctx_load;  // impossible (safe default)
  }
}

// This function never raises exceptions.
static u8 boolop(boolop_ty op) {
  switch (op) {
  case And: return Python_BoolOp_land;
  case Or:  return Python_BoolOp_lor;
  default:  return 0; // impossible
  }
}

// This function never raises exceptions.
static u8 unaryop(unaryop_ty op) {
  switch (op) {
  case Invert: return Python_UnaryOp_invert;
  case Not:    return Python_UnaryOp_not;
  case UAdd:   return Python_UnaryOp_uadd;
  case USub:   return Python_UnaryOp_usub;
  default:     return 0; // impossible
  }
}

// This function never raises exceptions.
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

// This function never raises exceptions.
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

// Returns List Op (or Nil for empty List).
// On failure, returns NULL with an exception set.
static lean_rc_ptr cmpops(struct state *st, asdl_int_seq *ops) {
  if (!ops)
    return mkNil();

  lean_object *arr = lean_alloc_array(0, ops->size);
  for (int i = 0; i < ops->size; i++) {
    u8 op = cmpop(static_cast<cmpop_ty>(ops->typed_elements[i]));
    arr = lean_array_push(arr, lean_box(op));
  }
  return lean_rc_ptr(lean_array_to_list(arr));
}

static lean_rc_ptr exprs(struct state *st, asdl_expr_seq *python);
static lean_rc_ptr keywords(struct state *st, asdl_keyword_seq *python);

// On failure, returns NULL with an exception set.
static lean_rc_ptr expr(struct state *st, struct _expr *python) {
  if (!python) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  auto old_pos = st->scope.pos;
  st->scope.pos.line = python->lineno;
  st->scope.pos.col = python->col_offset;

  lean_rc_ptr e;

  //static int indent = 0;
  //indent++;
  //for (int i = 0; i < indent; i++) printf(" ");
  //printf("EXPR %d %p (%d, %d)\n", python->kind, python, python->lineno, python->col_offset);
  switch (python->kind) {
    case Constant_kind: {
      lean_rc_ptr c = value(st, python->v.Constant.value);
      if (!c) break;

      e.reset(Python_Expr_const(c.release()));
      break;
    }
    // Names and attributes may be references which we need to track
    // We rely on the ctx value for a small optimization: we only need
    // to consider Loads
    case Name_kind: {
      lean_rc_ptr name;
      if (python->v.Name.ctx == Load) {
        struct ref r = reference(st, python);
        if (r.obj)
          name = std::move(r.name);
      }
      if (!name)
        name = py_strdup(python->v.Name.id);
      if (!name)
        break;
      e.reset(Python_Expr_name(name.release(), context(python->v.Name.ctx)));
      break;
    }

    case Attribute_kind: {
      lean_rc_ptr val = expr(st, python->v.Attribute.value);
      if (!val) break;

      lean_rc_ptr attr = py_strdup(python->v.Attribute.attr);
      if (!attr) break;

      e.reset(Python_Expr_attr(val.release(),
                               attr.release(),
                               context(python->v.Attribute.ctx)));

      if (python->v.Attribute.ctx == Load)
        reference(st, python);
      break;
    }

    // Containers: Tuple and List and Dict
    case Tuple_kind: {
      lean_rc_ptr elts = exprs(st, python->v.Tuple.elts);
      if (!elts) break;

      e.reset(Python_Expr_tuple(elts.release(), context(python->v.Tuple.ctx)));
      break;
    }
    case List_kind: {
      lean_rc_ptr elts = exprs(st, python->v.List.elts);
      if (!elts) break;

      e.reset(Python_Expr_list(elts.release(), context(python->v.List.ctx)));
      break;
    }
    case Dict_kind: {
      lean_rc_ptr keys = exprs(st, python->v.Dict.keys);
      if (!keys) break;

      lean_rc_ptr values = exprs(st, python->v.Dict.values);
      if (!values) break;

      e.reset(Python_Expr_dict(keys.release(), values.release()));
      break;
    }

    // Index expressions
    case Subscript_kind: {
      lean_rc_ptr tensor = expr(st, python->v.Subscript.value);
      if (!tensor) break;

      lean_rc_ptr slice = expr(st, python->v.Subscript.slice);
      if (!slice) break;

      e.reset(Python_Expr_subscript(tensor.release(), slice.release(), context(python->v.Subscript.ctx)));
      break;
    }
    case Slice_kind: {
      lean_rc_ptr lower; // optional
      if (python->v.Slice.lower) {
        lower = expr(st, python->v.Slice.lower);
        if (!lower) break;
      }
      lower = mkOption(std::move(lower));

      lean_rc_ptr upper; // optional
      if (python->v.Slice.upper) {
        upper = expr(st, python->v.Slice.upper);
        if (!upper) break;
      }
      upper = mkOption(std::move(upper));

      lean_rc_ptr step; // optional
      if (python->v.Slice.step) {
        step = expr(st, python->v.Slice.step);
        if (!step) break;
      }
      step = mkOption(std::move(step));

      e.reset(Python_Expr_slice(lower.release(),
                                upper.release(),
                                step.release()));
      break;
    }

    // Operators
    case BoolOp_kind: {
      lean_rc_ptr values = exprs(st, python->v.BoolOp.values);
      if (!values) break;

      e.reset(Python_Expr_boolOp(boolop(python->v.BoolOp.op),
                                 values.release()));
      break;
    }
    case BinOp_kind: {
      lean_rc_ptr left = expr(st, python->v.BinOp.left);
      if (!left) break;

      lean_rc_ptr right = expr(st, python->v.BinOp.right);
      if (!right) break;

      e.reset(Python_Expr_binOp(binop(python->v.BinOp.op), left.release(), right.release()));
      break;
    }
    case UnaryOp_kind: {
      lean_rc_ptr operand = expr(st, python->v.UnaryOp.operand);
      if (!operand) break;

      e.reset(Python_Expr_unaryOp(unaryop(python->v.UnaryOp.op), operand.release()));
      break;
    }
    case Compare_kind: {
      lean_rc_ptr left = expr(st, python->v.Compare.left);
      if (!left) break;

      lean_rc_ptr ops = cmpops(st, python->v.Compare.ops);
      if (!ops) break;

      lean_rc_ptr comparators = exprs(st, python->v.Compare.comparators);
      if (!comparators) break;

      e.reset(Python_Expr_compare(left.release(), ops.release(), comparators.release()));
      break;
    }

    // Condition expression
    case IfExp_kind: {
      lean_rc_ptr test = expr(st, python->v.IfExp.test);
      if (!test) break;

      lean_rc_ptr body = expr(st, python->v.IfExp.body);
      if (!body) break;

      lean_rc_ptr orelse = expr(st, python->v.IfExp.orelse);
      if (!orelse) break;

      e.reset(Python_Expr_ifExp(test.release(), body.release(), orelse.release()));
      break;
    }

    // Function calls
    case Call_kind: {
      lean_rc_ptr f = expr(st, python->v.Call.func);
      if (!f) break;

      lean_rc_ptr args = exprs(st, python->v.Call.args);
      if (!args) break;

      lean_rc_ptr kwords = keywords(st, python->v.Call.keywords);
      if (!kwords) break;

      e.reset(Python_Expr_call(f.release(), args.release(), kwords.release()));
      break;
    }

    // Tuple expansion *t
    case Starred_kind: {
      lean_rc_ptr col = expr(st, python->v.Starred.value);
      if (!col) break;

      e.reset(Python_Expr_starred(col.release(), context(python->v.Starred.ctx)));
      break;
    }

    // f-strings
    case FormattedValue_kind: {
      if (python->v.FormattedValue.format_spec) {
        syntax_error(st, "NKI does no support format specifiers");
        break;
      }
      lean_rc_ptr val = expr(st, python->v.FormattedValue.value);
      if (!val) break;

      int conv = python->v.FormattedValue.conversion;
      lean_rc_ptr l_conv =
        conv <= 0 ? mkNone() : mkOption(lean_rc_ptr(lean_unsigned_to_nat(conv)));

      e.reset(Python_Expr_format(val.release(), l_conv.release()));
      break;
    }
    case JoinedStr_kind: {
      lean_rc_ptr values = exprs(st, python->v.JoinedStr.values);
      if (!values) break;

      e.reset(Python_Expr_joined(values.release()));
      break;
    }

    default:
      syntax_error(st, "unsupported expression");
      break;
  }

  //for (int i = 0; i < indent; i++) printf(" ");
  //printf("expr %d %p\n", python->kind, python);
  //indent--;
  st->scope.pos = old_pos;
  return e ? lean_rc_ptr(Python_Expr_mk(e.release(), Pos(python).release())) : NULL;
}

// return List Expr (or Nil for empty List).
// On failure, returns NULL with an exception set.
static lean_rc_ptr exprs(struct state *st, asdl_expr_seq *python) {
  if (!python)
    return mkNil();

  auto arr = lean_rc_ptr(lean_alloc_array(0, python->size));
  for (int i = 0; i < python->size; i++) {
    lean_rc_ptr e = expr(st, python->typed_elements[i]);
    if (!e)
      return NULL;

    arr = lean_rc_ptr(lean_array_push(arr.release(), e.release()));
  }
  return lean_rc_ptr(lean_array_to_list(arr.release()));
}

// -----------------------------------------------------------------------------
// -- Keywords

// return Keyword
// On failure, returns NULL with an exception set.
static lean_rc_ptr keyword(struct state *st, keyword_ty python) {
  if (!python) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  // Note, we store the position, but do not update the context
  // The next expression also has a position, and we do not check the
  // keyword id

  lean_rc_ptr val = expr(st, python->value);
  if (!val)
    return NULL;

  // NULL means **kwarg
  lean_rc_ptr id;
  if (python->arg) {
    id = py_strdup(python->arg);
    if (!id)
      return NULL;
  }
  id = mkOption(std::move(id));

  return lean_rc_ptr(Python_Keyword_mk(id.release(), val.release(), Pos(python).release()));
}

// return List Keyword (or Nil for empty List).
// On failure, returns NULL with an exception set.
static lean_rc_ptr keywords(struct state *st, asdl_keyword_seq *python) {
  if (!python)
    return mkNil();

  auto arr = lean_rc_ptr(lean_alloc_array(0, python->size));
  for (int i = 0; i < python->size; i++) {
    lean_rc_ptr kw = keyword(st, python->typed_elements[i]);
    if (!kw)
      return NULL;
    arr = lean_rc_ptr(lean_array_push(arr.release(), kw.release()));
  }
  return lean_rc_ptr(lean_array_to_list(arr.release()));
}

// -----------------------------------------------------------------------------
// -- Arguments

// Return arg string
// On failure, returns NULL with an exception set.
static lean_rc_ptr arg(arg_ty python) {
  if (!python) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  return py_strdup(python->arg);
}

// Return list of arg strings (or Nil for empty list).
// On failure, returns NULL with an exception set.
static lean_rc_ptr arg_list(asdl_arg_seq *python) {
  if (!python)
    return mkNil();

  auto arr = lean_rc_ptr(lean_alloc_array(0, python->size));
  for (int i = 0; i < python->size; i++) {
    lean_rc_ptr str = arg(python->typed_elements[i]);
    if (!str)
      return NULL;
    arr = lean_rc_ptr(lean_array_push(arr.release(), str.release()));
  }
  return lean_rc_ptr(lean_array_to_list(arr.release()));
}

// Return Args
// On failure, returns NULL with an exception set.
static lean_rc_ptr args(struct state *st, arguments_ty python) {
  if (!python) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  lean_rc_ptr posonlyargs = arg_list(python->posonlyargs);
  if (!posonlyargs)
    return NULL;

  lean_rc_ptr args = arg_list(python->args);
  if (!args)
    return NULL;

  lean_rc_ptr vararg; // optional
  if (python->vararg) {
    vararg = arg(python->vararg);
    if (!vararg)
      return NULL;
  }
  vararg = mkOption(std::move(vararg));

  lean_rc_ptr kwonlyargs = arg_list(python->kwonlyargs);
  if (!kwonlyargs)
    return NULL;
    
  lean_rc_ptr kwarg; // optional
  if (python->kwarg) {
    kwarg = arg(python->kwarg);
    if (!kwarg)
      return NULL;
  }
  kwarg = mkOption(std::move(kwarg));

  lean_rc_ptr defaults = exprs(st, python->defaults);
  if (!defaults)
    return NULL;

  // TODO: this is a bug
  // The old version of gather computed the names of keyword defaults,
  // but this is not what the parser does.
  //as->kw_defaults = exprs(st, python->kw_defaults);
  lean_rc_ptr kw_defaults = mkNil();

  return lean_rc_ptr(Python_Args_mk(
    posonlyargs.release(),
    args.release(),
    defaults.release(),
    vararg.release(),
    kwonlyargs.release(),
    kw_defaults.release(),
    kwarg.release()));
}

// -----------------------------------------------------------------------------
// -- Statements

static lean_rc_ptr stmts(struct state *st, asdl_stmt_seq *python);


// Return Stmt.
// On failure, returns NULL with an exception set.
static lean_rc_ptr stmt(struct state *st, struct _stmt *python) {
  if (!python) {
    PyErr_Format(PyExc_TypeError, "NULL passed to %s", __func__);
    return NULL;
  }

  auto old_pos = st->scope.pos;
  st->scope.pos.line = python->lineno;
  st->scope.pos.col = python->col_offset;

  lean_rc_ptr s;

  //printf("STMT %d %p\n", python->kind, python);
  switch (python->kind) {
    case Pass_kind:
      lean_inc(Python_Stmt_pass);
      s.reset(Python_Stmt_pass);
      break;

    // Simple expressions
    case Expr_kind: {
      lean_rc_ptr e = expr(st, python->v.Return.value);
      if (!e) break;
      
      s.reset(Python_Stmt_expr(e.release()));
      break;
    }
    case Assert_kind: {
      // TODO capture message
      lean_rc_ptr e = expr(st, python->v.Assert.test);
      if (!e) break;

      s.reset(Python_Stmt_assert(e.release()));
      break;
    }
    case Return_kind: {
      lean_rc_ptr e = expr(st, python->v.Return.value);
      if (!e) break;

      s.reset(Python_Stmt_ret(e.release()));
      break;
    }

    // Assignments
    case Assign_kind: {
      lean_rc_ptr e = expr(st, python->v.Assign.value);
      if (!e) break;

      lean_rc_ptr targets = exprs(st, python->v.Assign.targets);
      if (!targets) break;

      s.reset(Python_Stmt_assign(targets.release(), e.release()));
      break;
    }
    case AugAssign_kind: {
      lean_rc_ptr x = expr(st, python->v.AugAssign.target);
      if (!x) break;

      u8 op = binop(python->v.AugAssign.op);
      if (op == 0) {
        syntax_error(st, "unsupported augmented assignment operator");
        break;
      }

      lean_rc_ptr e = expr(st, python->v.AugAssign.value);
      if (!e) break;

      s.reset(Python_Stmt_augAssign(x.release(), op, e.release()));
      break;
    }
    case AnnAssign_kind: {
      lean_rc_ptr x = expr(st, python->v.AnnAssign.target);
      if (!x) break;

      lean_rc_ptr ann = expr(st, python->v.AnnAssign.annotation);
      if (!ann) break;

      lean_rc_ptr value; // optional
      if (python->v.AnnAssign.value) {
        value = expr(st, python->v.AnnAssign.value);
        if (!value) break;
      }
      value = mkOption(std::move(value));

      s.reset(Python_Stmt_annAssign(x.release(), ann.release(), value.release()));
      break;
    }

    // If statements
    case If_kind: {
      lean_rc_ptr e = expr(st, python->v.If.test);
      if (!e) break;

      lean_rc_ptr body = stmts(st, python->v.If.body);
      if (!body) break;

      lean_rc_ptr orelse = stmts(st, python->v.If.orelse);
      if (!orelse) break;

      s.reset(Python_Stmt_ifStm(e.release(), body.release(), orelse.release()));
      break;
    }

    // For loops
    case For_kind: {
      lean_rc_ptr x = expr(st, python->v.For.target);
      if (!x) break;

      lean_rc_ptr iter = expr(st, python->v.For.iter);
      if (!iter) break;

      lean_rc_ptr body = stmts(st, python->v.For.body);
      if (!body) break;

      lean_rc_ptr orelse = stmts(st, python->v.For.orelse);
      if (!orelse) break;

      s.reset(Python_Stmt_forLoop(x.release(), iter.release(), body.release(), orelse.release()));
      break;
    }
    case Break_kind: {
      lean_inc(Python_Stmt_breakLoop);
      s.reset(Python_Stmt_breakLoop);
      break;
    }
    case Continue_kind: {
      lean_inc(Python_Stmt_continueLoop);
      s.reset(Python_Stmt_continueLoop);
      break;
    }

    case While_kind: {
      lean_rc_ptr test = expr(st, python->v.While.test);
      if (!test) break;

      lean_rc_ptr body = stmts(st, python->v.While.body);
      if (!body) break;

      lean_rc_ptr orelse = stmts(st, python->v.While.orelse);
      if (!orelse) break;

      s.reset(Python_Stmt_whileLoop(test.release(), body.release(), orelse.release()));
      break;
    }

    // TODO: do we need with?
    case With_kind:
      syntax_error(st, "NKI does not support 'with' statements at this time.");
      break;

    case FunctionDef_kind:
      syntax_error(st, "NKI does not support inner function definitions. Move function definition outside this function.");
      break;

    case ClassDef_kind:
      syntax_error(st, "NKI does not support 'class' definitions within a function. Move class definition outside this function.");
      break;

    case Delete_kind:
      syntax_error(st, "NKI does not support 'del' statements at this time.");
      break;

    case TypeAlias_kind:
      syntax_error(st, "NKI does not support 'type' statements at this time.");
      break;

    case AsyncFunctionDef_kind:
    case AsyncFor_kind:
    case AsyncWith_kind:
      syntax_error(st, "NKI does not support 'async'. Use only synchronous functions within kernels.");
      break;

    case Match_kind:
      syntax_error(st, "NKI does not support 'match' statements at this time. Use 'if/elif' or dict lookups instead.");
      break;

    case Raise_kind:
      syntax_error(st, "NKI does not support 'raise' statements. Use 'if/else' control flow within kernels, or 'assert' for fatal errors.");
      break;

    case Try_kind:
    case TryStar_kind:
      syntax_error(st, "NKI does not support 'try' statements. Use 'if/else' control flow within kernels.");
      break;

    case Import_kind:
    case ImportFrom_kind:
      syntax_error(st, "NKI does not support 'import' statements within a function. Move 'import' outside this function.");
      break;

    case Global_kind:
      syntax_error(st, "NKI does not support 'global' statements. Kernels cannot assign to global variables. Pass a dict between functions to share state.");
      break;

    case Nonlocal_kind:
      syntax_error(st, "NKI does not support 'nonlocal' statements. Kernels cannot assign to variables in nonlocal scope. Pass a dict between functions to share state.");
      break;

    default:
      syntax_error(st, "This statement is not supported in NKI.");
      break;
  }

  //printf("stmt %d %p\n", python->kind, python);
  st->scope.pos = old_pos;
  return s ? lean_rc_ptr(Python_Stmt_mk(s.release(), Pos(python).release())) : NULL;
}

// return List Stmt (or Nil for empty List).
// On failure, returns NULL with an exception set.
static lean_rc_ptr stmts(struct state *st, asdl_stmt_seq *python) {
  if (!python)
    return mkNil();

  auto arr = lean_rc_ptr(lean_alloc_array(0, python->size));
  for (int i = 0; i < python->size; i++) {
    lean_rc_ptr s = stmt(st, python->typed_elements[i]);
    if (!s)
      return NULL;
    arr = lean_rc_ptr(lean_array_push(arr.release(), s.release()));
  }
  return lean_rc_ptr(lean_array_to_list(arr.release()));
}

// -----------------------------------------------------------------------------
// -- Interface to the parser

// Return new reference to utility function.
// On failure, returns NULL with an exception set
static python_rc_ptr get_util(const char *name) {
  auto fe = python_rc_ptr(PyUnicode_FromString(MODULE_ROOT ".frontend"));
  if (!fe)
    return NULL;

  auto m = python_rc_ptr(PyImport_GetModule(fe.get()));
  if (!m)
    return NULL;

  return python_rc_ptr(PyObject_GetAttrString(m.get(), name));
}

// On failure, returns NULL with an exception set
static struct _mod* parse_def(struct state *st, python_rc_ptr &obj) {
  python_rc_ptr getsrc = get_util("_get_src");
  if (!getsrc)
    return NULL;
    
  auto args = python_rc_ptr(PyTuple_Pack(1, obj.get()));
  if (!args)
    return NULL;

  auto source = python_rc_ptr(PyObject_CallObject(getsrc.get(), args.get()));
  if (!source)
    return NULL;

  if (!PyTuple_Check(source.get()) || PyTuple_Size(source.get()) != 3) {
    PyErr_SetString(PyExc_RuntimeError, "Unexpected value from _get_src(), expected 3-tuple");
    return NULL;
  }

  // Note: Tuple_GetItem does not increment reference count
  PyObject *file = PyTuple_GetItem(source.get(), 0);
  PyObject *line = PyTuple_GetItem(source.get(), 1);
  PyObject *src  = PyTuple_GetItem(source.get(), 2);

  if (!file || !PyUnicode_Check(file) ||
      !line || !PyLong_Check(line) ||
      !src  || !PyUnicode_Check(src)) {
    PyErr_SetString(PyExc_RuntimeError, "Unexpected value from _get_src(), expected (str, int, str)");
    return NULL;
  }


  const char *file_str = PyUnicode_AsUTF8(file);
  const char *src_str = PyUnicode_AsUTF8(src);
  if (!file_str || !src_str)
    return NULL;

  _mod *m = parse_string(src_str, file);
  if (!m)
    return NULL;

  // everything checks out, enter new scope
  if (PyType_Check(obj.get())) {
    st->scope.cls = obj;
    st->scope.f = NULL;
  } else if (PyFunction_Check(obj.get())) {
    st->scope.cls = NULL;
    st->scope.f = obj;
  }
  st->scope.src = lean_rc_ptr(lean_mk_string(src_str));
  st->scope.file = lean_rc_ptr(lean_mk_string(file_str));
  st->scope.line_offset = PyLong_AsLong(line);
  st->scope.pos.line = 0;
  st->scope.pos.col = 0;

  return m;
}

// Returns Fun
// On failure, returns NULL with an exception set
static lean_rc_ptr function_(struct state *st, lean_rc_ptr name, struct _stmt *s) {
  lean_rc_ptr as = args(st, s->v.FunctionDef.args);
  if (!as)
    return NULL;

  // dont follow decorators
  st->ignore_refs = true;
  lean_rc_ptr decs = exprs(st, s->v.FunctionDef.decorator_list);
  st->ignore_refs = false;
  if (!decs)
    return NULL;

  lean_rc_ptr body = stmts(st, s->v.FunctionDef.body);
  if (!body || PyErr_Occurred())
    return NULL;

  // incref strings from scope, before Python_Fun_mk() steals a reference
  lean_rc_ptr file = st->scope.file;
  lean_rc_ptr src = st->scope.src;

  return lean_rc_ptr(Python_Fun_mk(
    name.release(),
    file.release(),
    lean_unsigned_to_nat(st->scope.line_offset),
    src.release(),
    decs.release(),
    as.release(),
    body.release()));
}

// Add Function to st->defs
// On failure, returns false with an exception set
static bool function_def(struct state *st, lean_rc_ptr name, struct _stmt *s) {
  lean_rc_ptr f = function_(st, name, s);
  if (!f) return false;

  state::definition &new_def = st->defs.emplace_back();
  new_def.str = std::move(name);
  new_def.type = state::definition::FUN;
  new_def.obj = std::move(f);

  return true;
}

// Returns Keyword
// On failure, returns NULL with an exception set
static lean_rc_ptr field(struct state *st, struct _expr *e) {
  if (e->kind != Name_kind) {
    syntax_error(st, "invalid left-hand side in assignment");
    return NULL;
  }

  lean_rc_ptr name = py_strdup(e->v.Name.id);
  if (!name)
    return NULL;


  auto obj = python_rc_ptr(PyObject_GetAttr(st->scope.cls.get(), e->v.Name.id));
  PyErr_Clear();

  lean_rc_ptr val;
  if (obj) {
    val = const_expr(st, obj.get());
    if (!val) {
      syntax_error(st, "Unsupported value in NKI class initializer");
      return NULL;
    }
  } else {
    lean_inc(Python_Const_none);
    val = lean_rc_ptr(Python_Expr_mk(Python_Expr_const(Python_Const_none), Pos(e).release()));
  }

  return lean_rc_ptr(Python_Keyword_mk(
    mkOption(std::move(name)).release(),
    val.release(),
    Pos(e).release()));
}


// Add Class to st->defs
// On failure, returns false with an exception set
static bool class_def(struct state *st, lean_rc_ptr name, struct _stmt *s) {
  if (s->v.ClassDef.keywords &&
      s->v.ClassDef.keywords->size > 0)
  {
    return true;
  }

  if (s->v.ClassDef.type_params &&
      s->v.ClassDef.type_params->size > 0)
  {
    return true;
  }

  // don't follow base classes or decorators
  st->ignore_refs = true;
  lean_rc_ptr bases = exprs(st, s->v.ClassDef.bases);
  lean_rc_ptr decs = bases ? exprs(st, s->v.ClassDef.decorator_list) : NULL;
  st->ignore_refs = false;
  if (!bases || !decs)
    return false;

  // Check that class inherits from allowed base classes
  if (s->v.ClassDef.bases && s->v.ClassDef.bases->size > 0) {
    bool valid_base = false;
    for (int i = 0; i < s->v.ClassDef.bases->size; i++) {
      struct _expr *base = s->v.ClassDef.bases->typed_elements[i];
      const char *base_name = NULL;
      if (base->kind == Name_kind) {
        base_name = PyUnicode_AsUTF8(base->v.Name.id);
      } else if (base->kind == Attribute_kind) {
        base_name = PyUnicode_AsUTF8(base->v.Attribute.attr);
      }
      if (base_name && (strstr(base_name, "NKIObject") ||
                       strstr(base_name, "Enum") ||
                       strstr(base_name, "IntEnum") ||
                       strstr(base_name, "NamedTuple"))) {
        valid_base = true;
        break;
      }
    }
    if (!valid_base) {
      return true;
    }
  } else {
    // Class has to inherit one of the above
    return true;
  }

  asdl_stmt_seq *python = s->v.ClassDef.body;
  auto fields = lean_rc_ptr(lean_mk_empty_array());
  auto methods = lean_rc_ptr(lean_mk_empty_array());

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
      syntax_error(st, "Expression statements not supported in NKI classes");
      return false;

    case Assign_kind: {
      if (s->v.Assign.targets == NULL ||
          s->v.Assign.targets->size != 1)
      {
        syntax_error(st, "invalid assignment in NKI class");
        return false;
      }
      lean_rc_ptr f = field(st, s->v.Assign.targets->typed_elements[0]);
      if (!f) return false;

      fields = lean_rc_ptr(lean_array_push(fields.release(), f.release()));
      break;
    }
    case AnnAssign_kind: {
      lean_rc_ptr f = field(st, s->v.AnnAssign.target);
      if (!f) return false;

      fields = lean_rc_ptr(lean_array_push(fields.release(), f.release()));
      break;
    }
    case FunctionDef_kind: {
      auto f = python_rc_ptr(PyObject_GetAttr(st->scope.cls.get(), s->v.FunctionDef.name));
      if (!f) return false;

      lean_rc_ptr m_name = py_method_name(name, f.get());
      if (!m_name) return false;

      st->scope.f = f;
      lean_rc_ptr m = function_(st, std::move(m_name), s);
      st->scope.f = NULL;
      if (!m) return false;

      methods = lean_rc_ptr(lean_array_push(methods.release(), m.release()));
      break;
    }
    default:
      syntax_error(st, "Statement not supported in NKI classes");
      return false;
    }
  }

  auto cls = lean_rc_ptr(Python_Class_mk(
    name.release(),
    bases.release(),
    decs.release(),
    lean_array_to_list(fields.release()),
    lean_array_to_list(methods.release())));

  state::definition &new_def = st->defs.emplace_back();
  new_def.str = std::move(name);
  new_def.type = state::definition::CLS;
  new_def.obj = std::move(cls);

  return true;
}

// Add definition to state.
// On failure, returns false with an exception set.
static bool definition(struct state *st, python_rc_ptr &obj) {
  // goto cleanup if anything goes wrong
  bool result = false;
  lean_rc_ptr name;
  struct _stmt *stmt = NULL;

  state::scope_item old_scope = st->scope;
  struct _mod *m = parse_def(st, obj);
  if (!m ||
      m->kind != Interactive_kind ||
      !m->v.Interactive.body ||
      m->v.Interactive.body->size != 1)
  {
    // failure to parse is not an error
    PyErr_Clear();
    result = true;
    goto cleanup;
  }

  stmt = m->v.Interactive.body->typed_elements[0];
  st->scope.pos.line = stmt->lineno;
  st->scope.pos.col = stmt->col_offset;

  name = py_def_name(obj.get());
  if (!name)
    goto cleanup;

  switch (stmt->kind) {
  case FunctionDef_kind:
    if (st->scope.f)
      result = function_def(st, std::move(name), stmt);
    break;
  case ClassDef_kind: {
    if (st->scope.cls)
      result = class_def(st, std::move(name), stmt);
    break;
    }

  default:
    syntax_error(st, "unsupported definition type");
    result = false;
    break;
  }

cleanup:
  if (m) free_python_ast(m);
  st->scope = old_scope;
  return result;
}

// ----------------------------------------------------------------------------
// -- Entry points

// On failure, returns false with an exception set.
bool specialize(struct kernel *k, PyObject *args, PyObject *kws, PyObject *grid, PyObject *schedule) {

  struct state st;

  // add main function to work list, and process arguments
  // potentially adding more dependencies to the work list
  add_work(&st, k->f);

  lean_rc_ptr l_args = args == Py_None ? mkNil() : const_exprs(&st, args);
  if (!l_args) {
    if (!PyErr_Occurred())
      PyErr_SetString(PyExc_RuntimeError, "Failed to process kernel arguments");
    return false;
  }

  lean_rc_ptr l_kwargs = kws == Py_None ? mkNil() : const_dict(&st, kws);
  if (!l_kwargs) {
    if (!PyErr_Occurred())
      PyErr_SetString(PyExc_RuntimeError, "Failed to process kernel keyword arguments");
    return false;
  }

  // Go through worklist, adding definitions
  // NOTE: using iterators (instead of range-based for loop), so we can safely add to list while we iterate
  for (auto work_it = st.worklist.begin(); work_it != st.worklist.end(); ++work_it) {
    if (!definition(&st, work_it->obj)) {
      if (!PyErr_Occurred())
        PyErr_SetString(PyExc_RuntimeError, "Failed to process kernel definition");
      return false;
    }
  }

  // Process additional kernel data from user
  // (ignoring any generated work items)
  long grid_val = 0;
  if (grid != Py_None) {
    grid_val = PyLong_AsLong(grid);
    if (grid_val < 0 || grid_val > 8) {
      PyErr_SetString(PyExc_ValueError, "grid must be between 0-8");
      return false;
    }
  }
  auto l_grid = lean_rc_ptr(lean_unsigned_to_nat((u32)grid_val));

  lean_rc_ptr l_sched = schedule == Py_None ? mkNil() : const_exprs(&st, schedule);
  if (!l_sched) {
    if (!PyErr_Occurred())
      PyErr_SetString(PyExc_RuntimeError, "Failed to process kernel schedule");
    return false;
  }

  if (PyErr_Occurred())
    return false;

  // Build the kernel object
  // from hereon we can't fail, so using lean_object* instead of lean_rc_ptr
  lean_object *fs = lean_mk_empty_array();
  lean_object *cs = lean_mk_empty_array();
  lean_object *gs = lean_mk_empty_array();
  for (auto &d : st.defs) {
    switch (d.type) {
    case state::definition::FUN: fs = lean_array_push(fs, d.obj.release()); break;
    case state::definition::CLS: cs = lean_array_push(cs, d.obj.release()); break;
    case state::definition::GLOBAL: gs = lean_array_push(gs, d.obj.release()); break;
    }
  }

  auto l_k = lean_rc_ptr(Python_Kernel_mk(
    py_def_name(k->f).release(),
    lean_array_to_list(fs),
    lean_array_to_list(cs),
    l_args.release(),
    l_kwargs.release(),
    lean_array_to_list(gs),
    l_grid.release(),
    l_sched.release()));

  // save the constructed kernel
  if (!k->lean_kernel) {
    k->lean_kernel = new lean_kernel();
  }
  k->lean_kernel->kernel = std::move(l_k);
  return true;
}

void free_lean_kernel(struct lean_kernel *l_kernel) {
  delete l_kernel;
}

extern "C" lean_object* nki_to_json(lean_object*);

// Returns Python string (or NULL, with an exception set)
PyObject* serialize_python(struct kernel *k) {
  if (!k->lean_kernel) {
    if (!specialize(k, Py_None, Py_None, Py_None, Py_None))
      return NULL;
  }

  if (!k->lean_kernel) {
    PyErr_SetString(PyExc_RuntimeError, "No valid kernel in serialize");
    return NULL;
  }

  // incref kernel, because nki_to_json() will steal a ref
  lean_object *l_kernel = k->lean_kernel->kernel.get();
  lean_inc(l_kernel);
  auto json = lean_rc_ptr(nki_to_json(l_kernel));

  return py_string_from_lean(std::move(json));
}

extern "C" lean_object* nki_trace(lean_object*, lean_object*, lean_object*);

// from util/io implemented in Init/System/IOError.lean
extern "C" lean_object* lean_io_error_to_string(lean_object*);

// Returns Python string (or NULL, with an exception set)
PyObject* trace(struct kernel *k, const char *dst_file) {
  if (!k->lean_kernel) {
    PyErr_SetString(PyExc_RuntimeError, "No valid kernel to serialize");
    return NULL;
  }

  auto file = lean_rc_ptr(lean_mk_string(dst_file));
  auto world = lean_rc_ptr(lean_io_mk_world());
  lean_rc_ptr l_kernel = k->lean_kernel->kernel;
  auto res = lean_rc_ptr(nki_trace(l_kernel.release(), file.release(), world.release()));

  if (lean_io_result_is_ok(res.get())) {
    auto str = lean_rc_ptr(lean_io_result_take_value(res.release()));
    return py_string_from_lean(std::move(str));
  } else {
    lean_object *err = lean_io_result_get_error(res.get()); // takes borrowed ref, returns borrowed ref
    lean_inc(err);
    auto str = lean_rc_ptr(lean_io_error_to_string(err));
    PyErr_SetString(PyExc_RuntimeError, lean_string_cstr(str.get()));
    return NULL;
  }
}
