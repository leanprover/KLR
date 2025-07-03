/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once

// frontend.h (this file) is to support .c files that do NOT require the Python C API.
// frontend_py.h is to support .c files that DO require the Python C API.

#include "stdc.h"
#include "region.h"

// Front-end version (place holder)
#define KLR_VERSION 1

// The place where we live
//#define MODULE_ROOT "neuronxcc.nki"
#define MODULE_ROOT ""

// Forward declarations
struct NKI_Kernel;
struct Python_Kernel;

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
