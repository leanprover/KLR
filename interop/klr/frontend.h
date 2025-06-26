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
static_assert(
    PY_MAJOR_VERSION == 3 &&
    PY_MINOR_VERSION >= 9 &&
    PY_MINOR_VERSION <= 12,
    "Unsupported Python Version");

#if PY_MINOR_VERSION == 9
#define Py_IsNone(x) ((x) == Py_None)
#define Py_IsTrue(x) ((x) == Py_True)
#endif

// Front-end version (place holder)
#define KLR_VERSION 1

// The place where we live
//#define MODULE_ROOT "neuronxcc.nki"
#define MODULE_ROOT ""

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

// peg_parser.c
struct _mod* parse_string(const char *str, PyObject* filename);
void free_python_ast(struct _mod *m);

// gather.c
bool gather(struct kernel *k);
bool specialize(struct kernel *k, PyObject *args, PyObject *kws);

// simplify.c
struct SimpResult {
  bool ok;
  const char *err;
  struct region *region;
  struct NKI_Kernel *kernel;
};
struct SimpResult simplify(struct Python_Kernel *py);

// serde.c
struct SerResult {
  bool ok;
  const char *err;
  u8* bytes;
  u64 size;
};
struct DesResult {
  bool ok;
  bool isNki;
  const char *err;
  struct region *region;
  union {
    struct Python_Kernel *python;
    struct NKI_Kernel *nki;
  };
};

struct SerResult serialize_python(const char *file, struct Python_Kernel *k);
struct DesResult deserialize_python(const u8 *buf, u64 size);

struct SerResult serialize_nki(const char *file, struct NKI_Kernel *k);
struct DesResult deserialize_nki(const u8 *buf, u64 size);
