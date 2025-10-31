/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once
#include "stdc.h"
#include "region.h"

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#if PY_MINOR_VERSION == 9
#define Py_IsNone(x) ((x) == Py_None)
#define Py_IsTrue(x) ((x) == Py_True)
#endif

// Front-end version (place holder)
#define KLR_VERSION 1

// The place where we live
#ifdef IS_NKI_REPO
#define MODULE_ROOT "nki._klr"
#else
#define MODULE_ROOT "klr"
#endif

// The front-end is accessed through the class Kernel; one instance
// per kernel. Each instance has a `struct kernel` on the C side.

struct kernel {
  PyObject_HEAD
  PyObject *f;   // Kernel function
  struct region *region;
  struct lean_kernel *lean_kernel;
};

// peg_parser.c
struct _mod* parse_string(const char *str, PyObject* filename);
void free_python_ast(struct _mod *m);

// gather.c
PyObject* specialize(struct kernel *k, PyObject *args, PyObject *kws, PyObject *arch, PyObject *grid, PyObject *schedule, PyObject *flags);
const char* serialize_python(struct kernel *k);
const char* trace(struct kernel *k, const char *dst_file, const char *dst_format);

// klr_ffi.c

// Initialize Lean and the KLR module.
// On failure, returns false with a Python exception set.
bool initialize_KLR_lean_ffi(void);

// Sanity tests
PyObject* lean_ffi_hello(PyObject *self, PyObject *args);
PyObject* lean_ffi_throw(PyObject *self, PyObject *args);
PyObject* lean_ffi_panic(PyObject *self, PyObject *args);
