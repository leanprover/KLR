/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "frontend.h"
#include "ast_python.h"

/*
Many of the things in peg_parser are also in libpython, some private, some
public. To avoid name conflicts, we create a single compilation unit with
everything declared static, except for the two functions at the bottom of
this file. This ensures our version of the PEG parser will not get confused
with the version in the user's libpython.
*/

#include "peg_parser/compat.c"
#include "peg_parser/token.c"
#include "peg_parser/ast_python.c"
#include "peg_parser/tokenizer.c"
#include "peg_parser/pegen.c"
#include "peg_parser/string_parser.c"
#include "peg_parser/action_helpers.c"
#include "peg_parser/parser.c"

// -- Public interface to our version of the PEG parser

struct _mod* parse_string(const char *str, PyObject* filename) {
  PyArena *arena = _PyArena_New();
  if (!arena)
    return NULL;

  struct _mod *result = _PyPegen_run_parser_from_string(str, filename, arena);
  if (result)
    result->arena = arena;
  else
    _PyArena_Free(arena);
  return result;
}

// Everything (including m) is in the region
void free_python_ast(struct _mod *m) {
  if (m)
    _PyArena_Free(m->arena);
}
