/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once

// frontend_py.h (this file) is to support .c files that require the Python C API.
// frontend.h is to support .c files that do NOT require the Python C API.

#include "frontend.h"

#define PY_SSIZE_T_CLEAN
#include <Python.h>
static_assert(
    PY_MAJOR_VERSION == 3 &&
    PY_MINOR_VERSION >= 9 &&
    PY_MINOR_VERSION <= 12,
    "Unsupported Python Version");

#if PY_MINOR_VERSION == 9
#define Py_IsNone(x) ((x) == Py_None)
#define Py_IsTrue(x) ((x) == Py_True)
#endif

// The front-end is accessed through the class Kernel; one instance
// per kernel. Each instance has a `struct kernel` on the C side.

struct kernel {
  PyObject_HEAD
  PyObject *f;   // Kernel function
  bool specialized;
  struct region *python_region;
  struct Python_Kernel *python_kernel;
  struct region *nki_region;
  struct NKI_Kernel *nki_kernel;
};

// gather.c
bool gather(struct kernel *k);
bool specialize(struct kernel *k, PyObject *args, PyObject *kws);

// peg_parser.c
struct _mod* parse_string(const char *str, PyObject* filename);
void free_python_ast(struct _mod *m);
