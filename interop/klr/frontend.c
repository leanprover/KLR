/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "frontend.h"

// This file defines the frontend Python extension module and the
// Kernel type contained therein.

// frontend.Kernel.__init__
static int kernel_init(struct kernel *self, PyObject *args, PyObject *kwds) {
  // kdws will be non-null if anything is passed by keyword
  if (kwds) {
    PyErr_BadArgument();
    return -1;
  }

  // We should have one argument, a function (not a callable)
  PyObject *f = NULL;
  if (!PyArg_ParseTuple(args, "O", &f)) {
    // Exception set by ParseTuple
    return -1;
  }
  if (!PyFunction_Check(f)) {
    Py_INCREF(PyExc_TypeError);
    PyErr_SetString(PyExc_TypeError, "parameter must be a function");
    return -1;
  }

  Py_INCREF(f);
  self->f = f;
  self->region = region_create();
  self->lean_kernel = NULL;
  return 0;
}

// Custom deallocator for Kernel type
static void kernel_dealloc(struct kernel *self) {
  if (!self) return;
  Py_XDECREF(self->f); // NULL is OK
  region_destroy(self->region);
  // TODO: free lean objects
  Py_TYPE(self)->tp_free((PyObject *) self);
}

// frontend.Kernel.specialize
// Provide arguments for kernel specialization
static PyObject* kernel_specialize(struct kernel *self, PyObject *args_tuple) {
  PyObject* args = Py_None;     // O
  PyObject* kwargs = Py_None;   // O
  PyObject* grid = Py_None;     // O
  PyObject* schedule = Py_None; // O
  PyObject* flags = Py_None;    // O

  if (!PyArg_ParseTuple(args_tuple, "|OOOOO", &args, &kwargs, &grid, &schedule, &flags)) {
      PyErr_SetString(PyExc_TypeError, "Failed to parse the arguments");
      return NULL;
  }

  if (args != Py_None && !PyTuple_Check(args)) {
      return NULL;
  }
  if (kwargs != Py_None && !PyDict_Check(kwargs)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: 'kwargs' must be a dictionary");
      return NULL;
  }
  if (grid != Py_None && !PyLong_Check(grid)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: 'grid' must be an int");
      return NULL;
  }
  if (schedule != Py_None && !PySequence_Check(schedule)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: 'schedule' must be a sequence");
      return NULL;
  }

  if (flags != Py_None && !PySequence_Check(flags)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: 'flags' must be a list of tuples");
      return NULL;
  }

  return specialize(self, args, kwargs, grid, schedule, flags);
}

// frontend.Kernel.serialize_python
static PyObject* kernel_serialize(struct kernel *self) {
  const char *json = serialize_python(self);
  if (json)
    return PyUnicode_FromString(json);
  else
    return NULL;
}

// frontend.Kernel.trace
static PyObject* kernel_trace(struct kernel *self, PyObject *args) {
  const char *dst_file = NULL;
  const char *dst_format = "cbor";
  if (!PyArg_ParseTuple(args, "s|s", &dst_file, &dst_format)) {
    return NULL;
  }

  const char *json = trace(self, dst_file, dst_format);
  if (json)
    return PyUnicode_FromString(json);
  else
    return NULL;
}

// frontend.version
// Return the current frontend version (place holder)
static PyObject* version(PyObject *self, PyObject *args) {
  (void)self;
  (void)args;
  return PyLong_FromLong(KLR_VERSION);
}

// ----------------------------------------------------------------------------
// -- Module Definition

// Internal Python utilities
// These definitions are added to the frontend module and are called
// during the gather step. No point in writing these in C as inspect
// and textwrap are pure python anyway.
// Note: C23 #embed would be nice here
// Note: These will no longer be needed when we upgrade the parser.
static const char utils[] = "\
import inspect\n\
import textwrap\n\
def _get_src(f):\n\
  file = inspect.getsourcefile(f)\n\
  src, line = inspect.getsourcelines(f)\n\
  return file, line, textwrap.dedent(''.join(src))\n\
";

static PyMethodDef KernelMethods[] = {
  { "specialize", (void*)kernel_specialize, METH_VARARGS,
    "Provide arguments for specializing kernel" },
  { "serialize_python", (void*)kernel_serialize, METH_NOARGS,
    "write Python AST to a file" },
  { "trace", (void*)kernel_trace, METH_VARARGS,
    "Trace kernel and generate output file" },
  { NULL, NULL, 0, NULL }
};

static PyTypeObject KernelType = {
  .ob_base = PyVarObject_HEAD_INIT(NULL, 0)
  .tp_name = "frontend.Kernel",
  .tp_doc = PyDoc_STR("NKI Kernel"),
  .tp_basicsize = sizeof(struct kernel),
  .tp_itemsize = 0,
  .tp_flags = Py_TPFLAGS_DEFAULT,
  .tp_new = PyType_GenericNew,
  .tp_init = (initproc) kernel_init,
  .tp_dealloc = (destructor) kernel_dealloc,
  .tp_methods = KernelMethods,
};

static PyMethodDef methods[] = {
  {"version", version, METH_NOARGS, "Return NKI Version"},
  {"_lean_ffi_hello", lean_ffi_hello, METH_NOARGS, "Sanity check of Lean FFI"},
  {"_lean_ffi_throw", lean_ffi_throw, METH_NOARGS, "Sanity check of Lean FFI error handling"},
  {"_lean_ffi_panic", lean_ffi_panic, METH_NOARGS, "Sanity check of Lean FFI error handling"},
  {NULL, NULL, 0, NULL}
};

static struct PyModuleDef module = {
  .m_base = PyModuleDef_HEAD_INIT,
  .m_name = "frontend",
  .m_doc = PyDoc_STR("NKI Frontend"),
  .m_size = -1,
  .m_methods = methods,
  .m_slots = NULL,
  .m_traverse = NULL,
  .m_clear = NULL,
  .m_free = NULL
};

PyMODINIT_FUNC PyInit_frontend(void) {
  // goto error if anything goes wrong
  PyObject *m = NULL;

  if (PyType_Ready(&KernelType) < 0) {
    goto error;
  }

  m = PyModule_Create(&module); // New reference
  if (!m) {
    goto error;
  }

  // This really can't fail, CPython will assert in debug builds
  // and segfault in production builds if dict is NULL.
  PyObject *dict = PyModule_GetDict(m); // Borrowed reference
  if (!dict) {
    goto error;
  }

  // Add Kernel object, do not decrement reference
  if (PyDict_SetItemString(dict, "Kernel", (PyObject*) &KernelType) < 0) {
    goto error;
  }

  // Add python utility functions
  PyObject *res = PyRun_String(utils, Py_file_input, dict, dict); // New reference
  if (!res)
    goto error;
  Py_DECREF(res);

  // Initialize Lean stuff
  if (initialize_KLR_lean_ffi() == false) {
    goto error;
  }

  // Success!
  return m;

error:
  Py_XDECREF(m);
  return NULL;
}
