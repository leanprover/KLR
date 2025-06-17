/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "frontend.h"
#include "topy_nki.h"

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
  self->nki_region = NULL;
  self->nki_kernel = NULL;

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
  if (self->nki_region)
    region_destroy(self->nki_region);
  Py_TYPE(self)->tp_free((PyObject *) self);
}

// frontend.Kernel.specialize
// Provide arguments for kernel specialization
static PyObject* kernel_specialize(struct kernel *self, PyObject *args, PyObject *kws) {
  if (!PyTuple_Check(args) || (kws && !PyDict_Check(kws))) {
    PyErr_BadArgument();
    return NULL;
  }

  if (!specialize(self, args, kws))
    return NULL;

  struct SimpResult res = simplify(self->python_kernel);
  if (!res.ok) {
    PyErr_SetString(PyExc_RuntimeError, res.err);
    return NULL;
  }

  self->nki_region = res.region;
  self->nki_kernel = res.kernel;
  self->specialized = true;
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

// frontend.Kernel.serialize
static PyObject* kernel_serialize(struct kernel *self, PyObject *args) {
  if (!self->specialized || !self->nki_kernel) {
    PyErr_SetString(PyExc_RuntimeError, "specialize must be called before serialize");
    return NULL;
  }
  const char *file = NULL;
  if (!PyArg_ParseTuple(args, "s", &file)) {
    // Exception set by ParseTuple
    return NULL;
  }

  struct SerResult res = serialize_nki(file, self->nki_kernel);
  if (!res.ok) {
    PyErr_SetString(PyExc_RuntimeError, res.err);
    return NULL;
  }

  PyObject *arr = PyByteArray_FromStringAndSize((const char*)res.bytes, res.size);
  free(res.bytes);
  return arr;
}

// frontend.version
// Return the current frontend version (place holder)
static PyObject* version(PyObject *self, PyObject *args) {
  (void)self;
  (void)args;
  return PyLong_FromLong(KLR_VERSION);
}

// frontend.deserialize
static PyObject* deserialize(PyObject *self, PyObject *args) {
  (void)self;
  PyObject *ba = NULL;
  if (!PyArg_ParseTuple(args, "Y", &ba)) {
    // Exception set by ParseTuple
    return NULL;
  }
  ssize_t size = PyByteArray_Size(ba);
  const u8* buf = (u8*)PyByteArray_AsString(ba);
  struct DesResult res = deserialize_nki(buf, size);
  if (!res.ok) {
    PyErr_SetString(PyExc_RuntimeError, res.err);
    return NULL;
  }

  PyObject *obj = NKI_Kernel_topy(res.nki);
  if (!obj)
    PyErr_SetString(PyExc_RuntimeError, "Could not construct Python AST");
  return obj;
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
def _bind_args(f, args, kwargs):\n\
  s = inspect.signature(f)\n\
  a = s.bind(*args, **kwargs)\n\
  a.apply_defaults()\n\
  return a.arguments\n\
";

static PyMethodDef KernelMethods[] = {
  { "_serialize_python", (void*)kernel_serialize_python, METH_VARARGS,
    "Serialize the intermediate Python Kernel to a ByteArray" },
  { "serialize", (void*)kernel_serialize, METH_VARARGS,
    "Serialize a NKI Kernel to a ByteArray" },
  { "specialize", (void*)kernel_specialize, METH_VARARGS|METH_KEYWORDS,
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
  {"deserialize", deserialize, METH_VARARGS, "Deserialize a NKI kernel from a bytearray"},
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
  if (PyType_Ready(&KernelType) < 0)
    return NULL;

  PyObject *m = PyModule_Create(&module);
  if (!m)
    return NULL;

  // This really can't fail, CPython will assert in debug builds
  // and segfault in production builds if dict is NULL.
  PyObject *dict = PyModule_GetDict(m);
  if (!dict) {
    PyErr_SetString(PyExc_SystemError, "frontend module has no dictionary");
    return NULL;
  }

  // Add Kernel object, do not decrement reference
  if (PyDict_SetItemString(dict, "Kernel", (PyObject*) &KernelType) < 0) {
    Py_DECREF(m);
    return NULL;
  }

  // Add python utility functions
  PyObject *res = PyRun_String(utils, Py_file_input, dict, dict);
  Py_DECREF(dict);
  if (!res) {
    Py_DECREF(m);
    return NULL;
  }
  Py_DECREF(res);
  return m;
}
