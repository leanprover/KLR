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
  self->specialized = false;
  self->python_region = NULL;
  self->python_kernel = NULL;

  if (!gather(self)) {
    if (!PyErr_Occurred())
      PyErr_SetString(PyExc_RuntimeError, "Unable to fetch NKI function from Python Environment");
    return -1;
  }
  return 0;
}

// Custom deallocator for Kernel type
static void kernel_dealloc(struct kernel *self) {
  if (!self) return;
  Py_XDECREF(self->f); // NULL is OK
  if (self->python_region)
    region_destroy(self->python_region);
  Py_TYPE(self)->tp_free((PyObject *) self);
}

// frontend.Kernel.specialize
// Provide arguments for kernel specialization
static PyObject* kernel_specialize(struct kernel *self, PyObject *args_tuple) {
  PyObject* args = NULL;
  PyObject* kwargs = NULL;
  PyObject* internal_kwargs = NULL;

  if (!PyArg_ParseTuple(args_tuple, "|OOO", &args, &kwargs, &internal_kwargs)) {
      return NULL;
  }

  if (args && args != Py_None && !PyTuple_Check(args)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: args argument must be a tuple");
      return NULL;
  }
  if (kwargs && kwargs != Py_None && !PyDict_Check(kwargs)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: kwargs argument must be a dictionary");
      return NULL;
  }
  if (internal_kwargs && internal_kwargs != Py_None && !PyDict_Check(internal_kwargs)) {
      PyErr_SetString(PyExc_TypeError, "Invalid Argument: internal_kwargs argument must be a dictionary");
      return NULL;
  }

  if (!specialize(self, args, kwargs, internal_kwargs))
    return NULL;

  return Py_None;
}

// frontend.Kernel._serialize_python
static PyObject* kernel_serialize_python(struct kernel *self, PyObject *args) {
  if (!self->python_kernel) {
    PyErr_SetString(PyExc_RuntimeError, "no python kernel available");
    return NULL;
  }
  const char *file = NULL;
  if (!PyArg_ParseTuple(args, "s", &file)) {
    // Exception set by ParseTuple
    return NULL;
  }

  struct SerResult res = serialize_python(file, self->python_kernel);
  if (!res.ok) {
    PyErr_SetString(PyExc_RuntimeError, res.err);
    return NULL;
  }

  free(res.bytes);
  return Py_None;
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
  { "_serialize_python", (void*)kernel_serialize_python, METH_VARARGS,
    "Serialize the intermediate Python Kernel to a ByteArray" },
  { "specialize", (void*)kernel_specialize, METH_VARARGS,
    "Provide arguments for specializing kernel" },
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
#ifdef IS_NKI_REPO
  {"_klr_trace", klr_trace, METH_VARARGS, "Trace Python to KLR"},
  {"_lean_ffi_hello", lean_ffi_hello, METH_NOARGS, "Sanity check of Lean FFI"},
  {"_lean_ffi_throw", lean_ffi_throw, METH_NOARGS, "Sanity check of Lean FFI error handling"},
  {"_lean_ffi_panic", lean_ffi_panic, METH_NOARGS, "Sanity check of Lean FFI error handling"},
#endif
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

#ifdef IS_NKI_REPO
  // Initialize Lean stuff
  if (initialize_KLR_lean_ffi() == false) {
    goto error;
  }
#endif

  // Success!
  return m;

error:
  Py_XDECREF(m);
  return NULL;
}
