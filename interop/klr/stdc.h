/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#pragma once

// A simple header file to check the C version and bring C standard
// definitions into scope.

#if __STDC__ != 1 || __STDC_VERSION__ < 201710L
#error Compiler does not support C17
#endif

#if defined(__STDC_NO_ATOMICS__)
#error Compiler does not support atomic types
#endif

// Standard definitions (free standing)

#include <stddef.h>
#include <stdarg.h>
#include <stdalign.h>
#include <stdnoreturn.h>

// Standard integer types

#include <stdbool.h>
#include <stdint.h>
#include <stdatomic.h>
#include <limits.h>

// Standard C utilites (free standing)

#include <errno.h>
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#ifndef __has_builtin
  #define __has_builtin(x) 0
#endif

#if __has_builtin(__builtin_expect)
  #define likely(x)   (__builtin_expect((x), 1))
  #define unlikely(x) (__builtin_expect((x), 0))
#else
  #define likely(x)   (x)
  #define unlikely(x) (x)
#endif

#define check_size(s,n) \
  static_assert(sizeof(s) == n, "sizeof "#s" unexpected")

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef float f32;
typedef double f64;

check_size(f32, 4);
check_size(f64, 8);
