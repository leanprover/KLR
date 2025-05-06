/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/

#define _GNU_SOURCE // for vasprintf

#include <lean/lean.h>
#include <stdarg.h>
#include <stdio.h>

lean_object* io_err(const char* fmt, ...) {
  char* msg = NULL;
  va_list args;
  va_start(args, fmt);
  const int bytes = vasprintf(&msg, fmt, args);
  va_end(args);
  lean_object *lean_msg;
  if (bytes < 0) {
    fprintf(stderr, "couldn't format error message: %s", fmt);
    lean_msg = lean_mk_string(fmt);
  } else {
    lean_msg = lean_mk_string(msg); // copies
    free(msg);
  }
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_msg));
}
  
