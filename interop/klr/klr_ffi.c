#include <lean/lean.h>

#include "frontend.h"

// forward declarations
lean_object* initialize_KLR_Compile(uint8_t builtin, lean_object* w);
void lean_initialize_runtime_module();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* klr_frontend_fail(lean_object*);
lean_object* klr_frontend_hello(lean_object*);
lean_object* klr_frontend_trace(lean_object*, lean_object*, lean_object*);

// Given a lean_io_result, sets a Python exception.
// Steals the reference to lean_io_result.
static void set_pyerr_from_lean_io_result_wprefix(lean_obj_arg l_io_result, const char *err_msg_prefix) {
  b_lean_obj_res l_io_error = lean_io_result_get_error(l_io_result); // borrows reference to arg, returns borrowed reference
  lean_inc_ref(l_io_error);
  lean_obj_res l_string = lean_io_error_to_string(l_io_error); // steals reference to arg, returns new reference
  const char *c_str = lean_string_cstr(l_string); // borrows reference to arg, returns borrowed c-str

  PyObject *py_exc_type = PyExc_RuntimeError;
  if (err_msg_prefix && err_msg_prefix[0] != 0) {
    PyErr_Format(py_exc_type, "%s: %s", err_msg_prefix, c_str);
  } else {
    PyErr_SetString(py_exc_type, c_str);
  }

  lean_dec(l_string);
  lean_dec(l_io_result);
}

// Given a lean_io_result, sets a Python exception.
// Steals the reference to lean_io_result.
static void set_pyerr_from_lean_io_result(lean_obj_arg l_io_result) {
  set_pyerr_from_lean_io_result_wprefix(l_io_result, NULL/*err_msg_prefix*/);
}

// Initialize Lean and the KLR module.
// Returns true if successful.
// Otherwise returns false and sets a Python exception
bool initialize_KLR_lean_ffi() {
  // Abort if Lean panics.
  // Better to be dead than living in a world of undefined behavior.
  setenv("LEAN_ABORT_ON_PANIC", "1", 1);

  // See:
  // https://lean-lang.org/doc/reference/4.22.0-rc2//Run-Time-Code/Foreign-Function-Interface/
  // https://github.com/leanprover/lean4/blob/master/src/lake/examples/reverse-ffi/main.c
  lean_initialize_runtime_module();
  uint8_t builtin = 1;
  lean_obj_res l_io_result = initialize_KLR_Compile(builtin, lean_io_mk_world());
  if (lean_io_result_is_ok(l_io_result)) {
    lean_dec_ref(l_io_result);
  } else {
    set_pyerr_from_lean_io_result_wprefix(l_io_result, "Lean initialization failed");
    return false;
  }
  lean_io_mark_end_initialization();

  return true;
}

PyObject* lean_ffi_hello(PyObject *self, PyObject *args) {
  (void)self;
  (void)args;

  lean_obj_res l_io_result = klr_frontend_hello(lean_io_mk_world());
  if (!lean_io_result_is_ok(l_io_result)) {
    set_pyerr_from_lean_io_result(l_io_result);
    return NULL;
  }

  lean_dec_ref(l_io_result);
  Py_RETURN_NONE;
}

PyObject* lean_ffi_fail(PyObject *self, PyObject *args) {
  (void)self;
  (void)args;

  lean_obj_res l_io_result = klr_frontend_fail(lean_io_mk_world());
  if (!lean_io_result_is_ok(l_io_result)) {
    set_pyerr_from_lean_io_result(l_io_result);
    return NULL;
  }

  lean_dec_ref(l_io_result);
  Py_RETURN_NONE;
}

PyObject* klr_trace(PyObject *self, PyObject *args) {
  (void)self;
  const char *src_python_ast_json_filepath = NULL;
  const char *dst_klir_filepath = NULL;
  if (!PyArg_ParseTuple(args, "ss", &src_python_ast_json_filepath, &dst_klir_filepath)) {
    return NULL;
  }

  // make FFI call
  lean_obj_res l_io_result = klr_frontend_trace(
    lean_mk_string(src_python_ast_json_filepath),
    lean_mk_string(dst_klir_filepath),
    lean_io_mk_world());
  if (!lean_io_result_is_ok(l_io_result)) {
    set_pyerr_from_lean_io_result(l_io_result); // steals reference to arg
    return NULL;
  }

  // translate lean string to python string
  lean_obj_res l_json_str = lean_io_result_take_value(l_io_result); // steals reference to arg, returns new reference
  PyObject *py_json_str = PyUnicode_FromString(lean_string_cstr(l_json_str));
  lean_dec(l_json_str);
  return py_json_str;
}
