#if 0
#define PyPARSE_YIELD_IS_KEYWORD 0x0001
#endif

#define PyPARSE_DONT_IMPLY_DEDENT 0x0002

#if 0
#define PyPARSE_WITH_IS_KEYWORD 0x0003
#define PyPARSE_PRINT_IS_FUNCTION 0x0004
#define PyPARSE_UNICODE_LITERALS 0x0008
#endif

#define PyPARSE_IGNORE_COOKIE 0x0010
#define PyPARSE_BARRY_AS_BDFL 0x0020
#define PyPARSE_TYPE_COMMENTS 0x0040
#define PyPARSE_ASYNC_HACKS 0x0080
#define PyPARSE_ALLOW_INCOMPLETE_INPUT 0x0100

#define CURRENT_POS (-5)

typedef struct _memo {
  int type;
  void *node;
  int mark;
  struct _memo *next;
} Memo;

typedef struct {
  int type;
  PyObject *bytes;
  int level;
  int lineno, col_offset, end_lineno, end_col_offset;
  Memo *memo;
  PyObject *metadata;
} Token;

typedef struct {
  const char *str;
  int type;
} KeywordToken;

typedef struct {
  struct {
    int lineno;
    char *comment; // The " <tag>" in "# type: ignore <tag>"
  } *items;
  size_t size;
  size_t num_items;
} growable_comment_array;

typedef struct {
  struct tok_state *tok;
  Token **tokens;
  int mark;
  int fill, size;
  PyArena *arena;
  KeywordToken **keywords;
  char **soft_keywords;
  int n_keyword_lists;
  int start_rule;
  int *errcode;
  int parsing_started;
  PyObject *normalize;
  int starting_lineno;
  int starting_col_offset;
  int error_indicator;
  int flags;
  int feature_version;
  growable_comment_array type_ignore_comments;
  Token *known_err_token;
  int level;
  int call_invalid_rules;
  int debug;
  struct _expr dummy_name;
} Parser;

// in parser.c
static void *_PyPegen_parse(Parser *);

typedef struct {
  cmpop_ty cmpop;
  expr_ty expr;
} CmpopExprPair;

typedef struct {
  expr_ty key;
  expr_ty value;
} KeyValuePair;

typedef struct {
  expr_ty key;
  pattern_ty pattern;
} KeyPatternPair;

typedef struct {
  arg_ty arg;
  expr_ty value;
} NameDefaultPair;

typedef struct {
  asdl_arg_seq *plain_names;
  asdl_seq *names_with_defaults; // asdl_seq* of NameDefaultsPair's
} SlashWithDefault;

typedef struct {
  arg_ty vararg;
  asdl_seq *kwonlyargs; // asdl_seq* of NameDefaultsPair's
  arg_ty kwarg;
} StarEtc;

typedef struct {
  operator_ty kind;
} AugOperator;
typedef struct {
  void *element;
  int is_keyword;
} KeywordOrStarred;

typedef struct {
  void *result;
  PyObject *metadata;
} ResultTokenWithMetadata;

// Error handling functions and APIs
typedef enum { STAR_TARGETS, DEL_TARGETS, FOR_TARGETS } TARGETS_TYPE;

// TOKENIZER ERRORS

static void _PyPegen_raise_tokenizer_init_error(PyObject *filename) {
  if (!(PyErr_ExceptionMatches(PyExc_LookupError) ||
        PyErr_ExceptionMatches(PyExc_SyntaxError) ||
        PyErr_ExceptionMatches(PyExc_ValueError) ||
        PyErr_ExceptionMatches(PyExc_UnicodeDecodeError))) {
    return;
  }
  PyObject *errstr = NULL;
  PyObject *tuple = NULL;
  PyObject *type;
  PyObject *value;
  PyObject *tback;
  PyErr_Fetch(&type, &value, &tback);
  errstr = PyObject_Str(value);
  if (!errstr) {
    goto error;
  }

  PyObject *tmp = Py_BuildValue("(OiiO)", filename, 0, -1, Py_None);
  if (!tmp) {
    goto error;
  }

  tuple = PyTuple_Pack(2, errstr, tmp);
  Py_DECREF(tmp);
  if (!value) {
    goto error;
  }
  PyErr_SetObject(PyExc_SyntaxError, tuple);

error:
  Py_XDECREF(type);
  Py_XDECREF(value);
  Py_XDECREF(tback);
  Py_XDECREF(errstr);
  Py_XDECREF(tuple);
}

static PyObject *get_error_line_from_tokenizer_buffers(Parser *p,
                                                       Py_ssize_t lineno) {
  /* If the file descriptor is interactive, the source lines of the current
   * (multi-line) statement are stored in p->tok->interactive_src_start.
   * If not, we're parsing from a string, which means that the whole source
   * is stored in p->tok->str. */
  assert((p->tok->fp == NULL && p->tok->str != NULL) || p->tok->fp != NULL);

  char *cur_line =
      p->tok->fp_interactive ? p->tok->interactive_src_start : p->tok->str;
  if (cur_line == NULL) {
    assert(p->tok->fp_interactive);
    // We can reach this point if the tokenizer buffers for interactive source
    // have not been initialized because we failed to decode the original source
    // with the given locale.
    return PyUnicode_FromStringAndSize("", 0);
  }

  Py_ssize_t relative_lineno =
      p->starting_lineno ? lineno - p->starting_lineno + 1 : lineno;
  const char *buf_end =
      p->tok->fp_interactive ? p->tok->interactive_src_end : p->tok->inp;

  if (buf_end < cur_line) {
    buf_end = cur_line + strlen(cur_line);
  }

  for (int i = 0; i < relative_lineno - 1; i++) {
    char *new_line = strchr(cur_line, '\n');
    // The assert is here for debug builds but the conditional that
    // follows is there so in release builds we do not crash at the cost
    // to report a potentially wrong line.
    assert(new_line != NULL && new_line + 1 < buf_end);
    if (new_line == NULL || new_line + 1 > buf_end) {
      break;
    }
    cur_line = new_line + 1;
  }

  char *next_newline;
  if ((next_newline = strchr(cur_line, '\n')) ==
      NULL) { // This is the last line
    next_newline = cur_line + strlen(cur_line);
  }
  return PyUnicode_DecodeUTF8(cur_line, next_newline - cur_line, "replace");
}

static Py_ssize_t
_PyPegen_byte_offset_to_character_offset_raw(const char *str,
                                             Py_ssize_t col_offset) {
  Py_ssize_t len = strlen(str);
  if (col_offset > len + 1) {
    col_offset = len + 1;
  }
  assert(col_offset >= 0);
  PyObject *text = PyUnicode_DecodeUTF8(str, col_offset, "replace");
  if (!text) {
    return -1;
  }
  Py_ssize_t size = PyUnicode_GET_LENGTH(text);
  Py_DECREF(text);
  return size;
}

static Py_ssize_t
_PyPegen_byte_offset_to_character_offset(PyObject *line,
                                         Py_ssize_t col_offset) {
  const char *str = PyUnicode_AsUTF8(line);
  if (!str) {
    return -1;
  }
  return _PyPegen_byte_offset_to_character_offset_raw(str, col_offset);
}

static int _PyPegen_fill_token(Parser *p);

static void *_PyPegen_raise_error_known_location(
    Parser *p, PyObject *errtype, Py_ssize_t lineno, Py_ssize_t col_offset,
    Py_ssize_t end_lineno, Py_ssize_t end_col_offset, const char *errmsg,
    va_list va) {
  // Bail out if we already have an error set.
  if (p->error_indicator && PyErr_Occurred()) {
    return NULL;
  }
  PyObject *value = NULL;
  PyObject *errstr = NULL;
  PyObject *error_line = NULL;
  PyObject *tmp = NULL;
  p->error_indicator = 1;

  if (end_lineno == CURRENT_POS) {
    end_lineno = p->tok->lineno;
  }
  if (end_col_offset == CURRENT_POS) {
    end_col_offset = p->tok->cur - p->tok->line_start;
  }

  errstr = PyUnicode_FromFormatV(errmsg, va);
  if (!errstr) {
    goto error;
  }

  if (p->tok->fp_interactive && p->tok->interactive_src_start != NULL) {
    error_line = get_error_line_from_tokenizer_buffers(p, lineno);
  } else if (p->start_rule == Py_file_input) {
    assert(0);
    // error_line = _PyErr_ProgramDecodedTextObject(p->tok->filename,
    //                                              (int) lineno,
    //                                              p->tok->encoding);
  }

  if (!error_line) {
    /* PyErr_ProgramTextObject was not called or returned NULL. If it was not
       called, then we need to find the error line from some other source,
       because p->start_rule != Py_file_input. If it returned NULL, then it
       either unexpectedly failed or we're parsing from a string or the REPL.
       There's a third edge case where we're actually parsing from a file, which
       has an E_EOF SyntaxError and in that case `PyErr_ProgramTextObject` fails
       because lineno points to last_file_line + 1, which does not physically
       exist */
    assert(p->tok->fp == NULL || p->tok->fp == stdin || p->tok->done == E_EOF);

    if (p->tok->lineno <= lineno && p->tok->inp > p->tok->buf) {
      Py_ssize_t size = p->tok->inp - p->tok->buf;
      error_line = PyUnicode_DecodeUTF8(p->tok->buf, size, "replace");
    } else if (p->tok->fp == NULL || p->tok->fp == stdin) {
      error_line = get_error_line_from_tokenizer_buffers(p, lineno);
    } else {
      error_line = PyUnicode_FromStringAndSize("", 0);
    }
    if (!error_line) {
      goto error;
    }
  }

  Py_ssize_t col_number = col_offset;
  Py_ssize_t end_col_number = end_col_offset;

  col_number = _PyPegen_byte_offset_to_character_offset(error_line, col_offset);
  if (col_number < 0) {
    goto error;
  }

  if (end_col_offset > 0) {
    end_col_number =
        _PyPegen_byte_offset_to_character_offset(error_line, end_col_offset);
    if (end_col_number < 0) {
      goto error;
    }
  }

  tmp = Py_BuildValue("(OnnNnn)", p->tok->filename, lineno, col_number,
                      error_line, end_lineno, end_col_number);
  if (!tmp) {
    goto error;
  }
  value = PyTuple_Pack(2, errstr, tmp);
  Py_DECREF(tmp);
  if (!value) {
    goto error;
  }
  PyErr_SetObject(errtype, value);

  Py_DECREF(errstr);
  Py_DECREF(value);
  return NULL;

error:
  Py_XDECREF(errstr);
  Py_XDECREF(error_line);
  return NULL;
}

static inline void *
RAISE_ERROR_KNOWN_LOCATION(Parser *p, PyObject *errtype, Py_ssize_t lineno,
                           Py_ssize_t col_offset, Py_ssize_t end_lineno,
                           Py_ssize_t end_col_offset, const char *errmsg, ...) {
  va_list va;
  va_start(va, errmsg);
  Py_ssize_t _col_offset =
      (col_offset == CURRENT_POS ? CURRENT_POS : col_offset + 1);
  Py_ssize_t _end_col_offset =
      (end_col_offset == CURRENT_POS ? CURRENT_POS : end_col_offset + 1);
  _PyPegen_raise_error_known_location(p, errtype, lineno, _col_offset,
                                      end_lineno, _end_col_offset, errmsg, va);
  va_end(va);
  return NULL;
}

static void *_PyPegen_raise_error(Parser *p, PyObject *errtype, int use_mark,
                                  const char *errmsg, ...) {
  // Bail out if we already have an error set.
  if (p->error_indicator && PyErr_Occurred()) {
    return NULL;
  }
  if (p->fill == 0) {
    va_list va;
    va_start(va, errmsg);
    _PyPegen_raise_error_known_location(p, errtype, 0, 0, 0, -1, errmsg, va);
    va_end(va);
    return NULL;
  }
  if (use_mark && p->mark == p->fill && _PyPegen_fill_token(p) < 0) {
    p->error_indicator = 1;
    return NULL;
  }
  Token *t = p->known_err_token != NULL
                 ? p->known_err_token
                 : p->tokens[use_mark ? p->mark : p->fill - 1];
  Py_ssize_t col_offset;
  Py_ssize_t end_col_offset = -1;
  if (t->col_offset == -1) {
    if (p->tok->cur == p->tok->buf) {
      col_offset = 0;
    } else {
      const char *start = p->tok->buf ? p->tok->line_start : p->tok->buf;
      col_offset = Py_SAFE_DOWNCAST(p->tok->cur - start, intptr_t, int);
    }
  } else {
    col_offset = t->col_offset + 1;
  }

  if (t->end_col_offset != -1) {
    end_col_offset = t->end_col_offset + 1;
  }

  va_list va;
  va_start(va, errmsg);
  _PyPegen_raise_error_known_location(p, errtype, t->lineno, col_offset,
                                      t->end_lineno, end_col_offset, errmsg,
                                      va);
  va_end(va);

  return NULL;
}

#define RAISE_SYNTAX_ERROR(msg, ...)                                           \
  _PyPegen_raise_error(p, PyExc_SyntaxError, 0, msg, ##__VA_ARGS__)
#define RAISE_INDENTATION_ERROR(msg, ...)                                      \
  _PyPegen_raise_error(p, PyExc_IndentationError, 0, msg, ##__VA_ARGS__)
#define RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN(msg, ...)                             \
  _PyPegen_raise_error(p, PyExc_SyntaxError, 1, msg, ##__VA_ARGS__)
#define RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, msg, ...)                         \
  RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, (a)->lineno,                \
                             (a)->col_offset, (b)->end_lineno,                 \
                             (b)->end_col_offset, msg, ##__VA_ARGS__)
#define RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, msg, ...)                         \
  RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, (a)->lineno,                \
                             (a)->col_offset, (a)->end_lineno,                 \
                             (a)->end_col_offset, msg, ##__VA_ARGS__)
#define RAISE_SYNTAX_ERROR_STARTING_FROM(a, msg, ...)                          \
  RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, (a)->lineno,                \
                             (a)->col_offset, CURRENT_POS, CURRENT_POS, msg,   \
                             ##__VA_ARGS__)
#define RAISE_SYNTAX_ERROR_INVALID_TARGET(type, e)                             \
  _RAISE_SYNTAX_ERROR_INVALID_TARGET(p, type, e)

static inline void raise_unclosed_parentheses_error(Parser *p) {
  int error_lineno = p->tok->parenlinenostack[p->tok->level - 1];
  int error_col = p->tok->parencolstack[p->tok->level - 1];
  RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, error_lineno, error_col,
                             error_lineno, -1, "'%c' was never closed",
                             p->tok->parenstack[p->tok->level - 1]);
}

static int _Pypegen_tokenizer_error(Parser *p) {
  if (PyErr_Occurred()) {
    return -1;
  }

  const char *msg = NULL;
  PyObject *errtype = PyExc_SyntaxError;
  Py_ssize_t col_offset = -1;
  p->error_indicator = 1;
  switch (p->tok->done) {
  case E_TOKEN:
    msg = "invalid token";
    break;
  case E_EOF:
    if (p->tok->level) {
      raise_unclosed_parentheses_error(p);
    } else {
      RAISE_SYNTAX_ERROR("unexpected EOF while parsing");
    }
    return -1;
  case E_DEDENT:
    RAISE_INDENTATION_ERROR(
        "unindent does not match any outer indentation level");
    return -1;
  case E_INTR:
    if (!PyErr_Occurred()) {
      PyErr_SetNone(PyExc_KeyboardInterrupt);
    }
    return -1;
  case E_NOMEM:
    PyErr_NoMemory();
    return -1;
  case E_TABSPACE:
    errtype = PyExc_TabError;
    msg = "inconsistent use of tabs and spaces in indentation";
    break;
  case E_TOODEEP:
    errtype = PyExc_IndentationError;
    msg = "too many levels of indentation";
    break;
  case E_LINECONT: {
    col_offset = p->tok->cur - p->tok->buf - 1;
    msg = "unexpected character after line continuation character";
    break;
  }
  case 29: // E_COLUMNOVERFLOW:
    PyErr_SetString(PyExc_OverflowError,
                    "Parser column offset overflow - source line is too big");
    return -1;
  default:
    msg = "unknown parsing error";
  }

  RAISE_ERROR_KNOWN_LOCATION(p, errtype, p->tok->lineno,
                             col_offset >= 0 ? col_offset : 0, p->tok->lineno,
                             -1, msg);
  return -1;
}

static int _Pypegen_raise_decode_error(Parser *p) {
  assert(PyErr_Occurred());
  const char *errtype = NULL;
  if (PyErr_ExceptionMatches(PyExc_UnicodeError)) {
    errtype = "unicode error";
  } else if (PyErr_ExceptionMatches(PyExc_ValueError)) {
    errtype = "value error";
  }
  if (errtype) {
    PyObject *type;
    PyObject *value;
    PyObject *tback;
    PyObject *errstr;
    PyErr_Fetch(&type, &value, &tback);
    errstr = PyObject_Str(value);
    if (errstr) {
      RAISE_SYNTAX_ERROR("(%s) %U", errtype, errstr);
      Py_DECREF(errstr);
    } else {
      PyErr_Clear();
      RAISE_SYNTAX_ERROR("(%s) unknown error", errtype);
    }
    Py_XDECREF(type);
    Py_XDECREF(value);
    Py_XDECREF(tback);
  }

  return -1;
}

static int _PyPegen_tokenize_full_source_to_check_for_errors(Parser *p) {
  // Tokenize the whole input to see if there are any tokenization
  // errors such as mistmatching parentheses. These will get priority
  // over generic syntax errors only if the line number of the error is
  // before the one that we had for the generic error.

  // We don't want to tokenize to the end for interactive input
  if (p->tok->prompt != NULL) {
    return 0;
  }

  PyObject *type, *value, *traceback;
  PyErr_Fetch(&type, &value, &traceback);

  Token *current_token =
      p->known_err_token != NULL ? p->known_err_token : p->tokens[p->fill - 1];
  Py_ssize_t current_err_line = current_token->lineno;

  int ret = 0;
  struct token new_token;
  _PyToken_Init(&new_token);

  for (;;) {
    switch (_PyTokenizer_Get(p->tok, &new_token)) {
    case ERRORTOKEN:
      if (PyErr_Occurred()) {
        ret = -1;
        goto exit;
      }
      if (p->tok->level != 0) {
        int error_lineno = p->tok->parenlinenostack[p->tok->level - 1];
        if (current_err_line > error_lineno) {
          raise_unclosed_parentheses_error(p);
          ret = -1;
          goto exit;
        }
      }
      break;
    case ENDMARKER:
      break;
    default:
      continue;
    }
    break;
  }

exit:
  _PyToken_Free(&new_token);
  // If we're in an f-string, we want the syntax error in the expression part
  // to propagate, so that tokenizer errors (like expecting '}') that happen
  // afterwards do not swallow it.
  if (PyErr_Occurred() && p->tok->tok_mode_stack_index <= 0) {
    Py_XDECREF(value);
    Py_XDECREF(type);
    Py_XDECREF(traceback);
  } else {
    PyErr_Restore(type, value, traceback);
  }
  return ret;
}

// PARSER ERRORS

static inline void *CHECK_CALL(Parser *p, void *result) {
  if (result == NULL) {
    assert(PyErr_Occurred());
    p->error_indicator = 1;
  }
  return result;
}

/* This is needed for helper functions that are allowed to
   return NULL without an error. Example: _PyPegen_seq_extract_starred_exprs */
static inline void *CHECK_CALL_NULL_ALLOWED(Parser *p, void *result) {
  if (result == NULL && PyErr_Occurred()) {
    p->error_indicator = 1;
  }
  return result;
}

#define CHECK(type, result) ((type)CHECK_CALL(p, result))
#define CHECK_NULL_ALLOWED(type, result)                                       \
  ((type)CHECK_CALL_NULL_ALLOWED(p, result))

static void _Pypegen_set_syntax_error(Parser *p, Token *last_token) {
  // Existing sintax error
  if (PyErr_Occurred()) {
    // Prioritize tokenizer errors to custom syntax errors raised
    // on the second phase only if the errors come from the parser.
    int is_tok_ok = (p->tok->done == E_DONE || p->tok->done == E_OK);
    if (is_tok_ok && PyErr_ExceptionMatches(PyExc_SyntaxError)) {
      _PyPegen_tokenize_full_source_to_check_for_errors(p);
    }
    // Propagate the existing syntax error.
    return;
  }
  // Initialization error
  if (p->fill == 0) {
    RAISE_SYNTAX_ERROR("error at start before reading any input");
  }
  // Parser encountered EOF (End of File) unexpectedtly
  if (last_token->type == ERRORTOKEN && p->tok->done == E_EOF) {
    if (p->tok->level) {
      raise_unclosed_parentheses_error(p);
    } else {
      RAISE_SYNTAX_ERROR("unexpected EOF while parsing");
    }
    return;
  }
  // Indentation error in the tokenizer
  if (last_token->type == INDENT || last_token->type == DEDENT) {
    RAISE_INDENTATION_ERROR(last_token->type == INDENT ? "unexpected indent"
                                                       : "unexpected unindent");
    return;
  }
  // Unknown error (generic case)

  // Use the last token we found on the first pass to avoid reporting
  // incorrect locations for generic syntax errors just because we reached
  // further away when trying to find specific syntax errors in the second
  // pass.
  RAISE_SYNTAX_ERROR_KNOWN_LOCATION(last_token, "invalid syntax");
  // _PyPegen_tokenize_full_source_to_check_for_errors will override the
  // existing generic SyntaxError we just raised if errors are found.
  _PyPegen_tokenize_full_source_to_check_for_errors(p);
}

static const char *_PyPegen_get_expr_name(expr_ty e) {
  assert(e != NULL);
  switch (e->kind) {
  case Attribute_kind:
    return "attribute";
  case Subscript_kind:
    return "subscript";
  case Starred_kind:
    return "starred";
  case Name_kind:
    return "name";
  case List_kind:
    return "list";
  case Tuple_kind:
    return "tuple";
  case Lambda_kind:
    return "lambda";
  case Call_kind:
    return "function call";
  case BoolOp_kind:
  case BinOp_kind:
  case UnaryOp_kind:
    return "expression";
  case GeneratorExp_kind:
    return "generator expression";
  case Yield_kind:
  case YieldFrom_kind:
    return "yield expression";
  case Await_kind:
    return "await expression";
  case ListComp_kind:
    return "list comprehension";
  case SetComp_kind:
    return "set comprehension";
  case DictComp_kind:
    return "dict comprehension";
  case Dict_kind:
    return "dict literal";
  case Set_kind:
    return "set display";
  case JoinedStr_kind:
  case FormattedValue_kind:
    return "f-string expression";
  case Constant_kind: {
    PyObject *value = e->v.Constant.value;
    if (value == Py_None) {
      return "None";
    }
    if (value == Py_False) {
      return "False";
    }
    if (value == Py_True) {
      return "True";
    }
    if (value == Py_Ellipsis) {
      return "ellipsis";
    }
    return "literal";
  }
  case Compare_kind:
    return "comparison";
  case IfExp_kind:
    return "conditional expression";
  case NamedExpr_kind:
    return "named expression";
  default:
    PyErr_Format(PyExc_SystemError,
                 "unexpected expression in assignment %d (line %d)", e->kind,
                 e->lineno);
    return NULL;
  }
}

static expr_ty _PyPegen_get_invalid_target(expr_ty e,
                                           TARGETS_TYPE targets_type) {
  if (e == NULL) {
    return NULL;
  }

#define VISIT_CONTAINER(CONTAINER, TYPE)                                       \
  do {                                                                         \
    Py_ssize_t len = asdl_seq_LEN((CONTAINER)->v.TYPE.elts);                   \
    for (Py_ssize_t i = 0; i < len; i++) {                                     \
      expr_ty other = asdl_seq_GET((CONTAINER)->v.TYPE.elts, i);               \
      expr_ty child = _PyPegen_get_invalid_target(other, targets_type);        \
      if (child != NULL) {                                                     \
        return child;                                                          \
      }                                                                        \
    }                                                                          \
  } while (0)

  // We only need to visit List and Tuple nodes recursively as those
  // are the only ones that can contain valid names in targets when
  // they are parsed as expressions. Any other kind of expression
  // that is a container (like Sets or Dicts) is directly invalid and
  // we don't need to visit it recursively.

  switch (e->kind) {
  case List_kind:
    VISIT_CONTAINER(e, List);
    return NULL;
  case Tuple_kind:
    VISIT_CONTAINER(e, Tuple);
    return NULL;
  case Starred_kind:
    if (targets_type == DEL_TARGETS) {
      return e;
    }
    return _PyPegen_get_invalid_target(e->v.Starred.value, targets_type);
  case Compare_kind:
    // This is needed, because the `a in b` in `for a in b` gets parsed
    // as a comparison, and so we need to search the left side of the comparison
    // for invalid targets.
    if (targets_type == FOR_TARGETS) {
      cmpop_ty cmpop = (cmpop_ty)asdl_seq_GET(e->v.Compare.ops, 0);
      if (cmpop == In) {
        return _PyPegen_get_invalid_target(e->v.Compare.left, targets_type);
      }
      return NULL;
    }
    return e;
  case Name_kind:
  case Subscript_kind:
  case Attribute_kind:
    return NULL;
  default:
    return e;
  }
}

static inline void *
_RAISE_SYNTAX_ERROR_INVALID_TARGET(Parser *p, TARGETS_TYPE type, void *e) {
  expr_ty invalid_target =
      CHECK_NULL_ALLOWED(expr_ty, _PyPegen_get_invalid_target(e, type));
  if (invalid_target != NULL) {
    const char *msg;
    if (type == STAR_TARGETS || type == FOR_TARGETS) {
      msg = "cannot assign to %s";
    } else {
      msg = "cannot delete %s";
    }
    return RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
        invalid_target, msg, _PyPegen_get_expr_name(invalid_target));
    return RAISE_SYNTAX_ERROR_KNOWN_LOCATION(invalid_target, "invalid syntax");
  }
  return NULL;
}

static void _Pypegen_stack_overflow(Parser *p) {
  p->error_indicator = 1;
  PyErr_SetString(
      PyExc_MemoryError,
      "Parser stack overflowed - Python source too complex to parse");
}
// Internal parser functions

static asdl_stmt_seq *_PyPegen_interactive_exit(Parser *p) {
  if (p->errcode) {
    *(p->errcode) = E_EOF;
  }
  return NULL;
}

// Here, mark is the start of the node, while p->mark is the end.
// If node==NULL, they should be the same.
static int _PyPegen_insert_memo(Parser *p, int mark, int type, void *node) {
  // Insert in front
  Memo *m = _PyArena_Malloc(p->arena, sizeof(Memo));
  if (m == NULL) {
    return -1;
  }
  m->type = type;
  m->node = node;
  m->mark = p->mark;
  m->next = p->tokens[mark]->memo;
  p->tokens[mark]->memo = m;
  return 0;
}

// Like _PyPegen_insert_memo(), but updates an existing node if found.
static int _PyPegen_update_memo(Parser *p, int mark, int type, void *node) {
  for (Memo *m = p->tokens[mark]->memo; m != NULL; m = m->next) {
    if (m->type == type) {
      // Update existing node.
      m->node = node;
      m->mark = p->mark;
      return 0;
    }
  }
  // Insert new node.
  return _PyPegen_insert_memo(p, mark, type, node);
}

static int init_normalization(Parser *p) {
  if (p->normalize) {
    return 1;
  }
  p->normalize = _PyImport_GetModuleAttrString("unicodedata", "normalize");
  if (!p->normalize) {
    return 0;
  }
  return 1;
}

static int growable_comment_array_init(growable_comment_array *arr,
                                       size_t initial_size) {
  assert(initial_size > 0);
  arr->items = PyMem_Malloc(initial_size * sizeof(*arr->items));
  arr->size = initial_size;
  arr->num_items = 0;

  return arr->items != NULL;
}

static int growable_comment_array_add(growable_comment_array *arr, int lineno,
                                      char *comment) {
  if (arr->num_items >= arr->size) {
    size_t new_size = arr->size * 2;
    void *new_items_array =
        PyMem_Realloc(arr->items, new_size * sizeof(*arr->items));
    if (!new_items_array) {
      return 0;
    }
    arr->items = new_items_array;
    arr->size = new_size;
  }

  arr->items[arr->num_items].lineno = lineno;
  arr->items[arr->num_items].comment = comment; // Take ownership
  arr->num_items++;
  return 1;
}

static void growable_comment_array_deallocate(growable_comment_array *arr) {
  for (unsigned i = 0; i < arr->num_items; i++) {
    PyMem_Free(arr->items[i].comment);
  }
  PyMem_Free(arr->items);
}

static int _get_keyword_or_name_type(Parser *p, struct token *new_token) {
  int name_len = new_token->end_col_offset - new_token->col_offset;
  assert(name_len > 0);

  if (name_len >= p->n_keyword_lists || p->keywords[name_len] == NULL ||
      p->keywords[name_len]->type == -1) {
    return NAME;
  }
  for (KeywordToken *k = p->keywords[name_len]; k != NULL && k->type != -1;
       k++) {
    if (strncmp(k->str, new_token->start, name_len) == 0) {
      return k->type;
    }
  }
  return NAME;
}

static int initialize_token(Parser *p, Token *parser_token,
                            struct token *new_token, int token_type) {
  assert(parser_token != NULL);

  parser_token->type = (token_type == NAME)
                           ? _get_keyword_or_name_type(p, new_token)
                           : token_type;
  parser_token->bytes = PyBytes_FromStringAndSize(
      new_token->start, new_token->end - new_token->start);
  if (parser_token->bytes == NULL) {
    return -1;
  }
  if (_PyArena_AddPyObject(p->arena, parser_token->bytes) < 0) {
    Py_DECREF(parser_token->bytes);
    return -1;
  }

  parser_token->metadata = NULL;
  if (new_token->metadata != NULL) {
    if (_PyArena_AddPyObject(p->arena, new_token->metadata) < 0) {
      Py_DECREF(parser_token->metadata);
      return -1;
    }
    parser_token->metadata = new_token->metadata;
    new_token->metadata = NULL;
  }

  parser_token->level = new_token->level;
  parser_token->lineno = new_token->lineno;
  parser_token->col_offset =
      p->tok->lineno == p->starting_lineno
          ? p->starting_col_offset + new_token->col_offset
          : new_token->col_offset;
  parser_token->end_lineno = new_token->end_lineno;
  parser_token->end_col_offset =
      p->tok->lineno == p->starting_lineno
          ? p->starting_col_offset + new_token->end_col_offset
          : new_token->end_col_offset;

  p->fill += 1;

  if (token_type == ERRORTOKEN && p->tok->done == E_DECODE) {
    return _Pypegen_raise_decode_error(p);
  }

  return (token_type == ERRORTOKEN ? _Pypegen_tokenizer_error(p) : 0);
}

static int _resize_tokens_array(Parser *p) {
  int newsize = p->size * 2;
  Token **new_tokens = PyMem_Realloc(p->tokens, newsize * sizeof(Token *));
  if (new_tokens == NULL) {
    PyErr_NoMemory();
    return -1;
  }
  p->tokens = new_tokens;

  for (int i = p->size; i < newsize; i++) {
    p->tokens[i] = PyMem_Calloc(1, sizeof(Token));
    if (p->tokens[i] == NULL) {
      p->size = i; // Needed, in order to cleanup correctly after parser fails
      PyErr_NoMemory();
      return -1;
    }
  }
  p->size = newsize;
  return 0;
}

static int _PyPegen_fill_token(Parser *p) {
  struct token new_token;
  _PyToken_Init(&new_token);
  int type = _PyTokenizer_Get(p->tok, &new_token);

  // Record and skip '# type: ignore' comments
  while (type == TYPE_IGNORE) {
    Py_ssize_t len = new_token.end_col_offset - new_token.col_offset;
    char *tag = PyMem_Malloc(len + 1);
    if (tag == NULL) {
      PyErr_NoMemory();
      goto error;
    }
    strncpy(tag, new_token.start, len);
    tag[len] = '\0';
    // Ownership of tag passes to the growable array
    if (!growable_comment_array_add(&p->type_ignore_comments, p->tok->lineno,
                                    tag)) {
      PyErr_NoMemory();
      goto error;
    }
    type = _PyTokenizer_Get(p->tok, &new_token);
  }

  // If we have reached the end and we are in single input mode we need to
  // insert a newline and reset the parsing
  if (p->start_rule == Py_single_input && type == ENDMARKER &&
      p->parsing_started) {
    type = NEWLINE; /* Add an extra newline */
    p->parsing_started = 0;

    if (p->tok->indent && !(p->flags & PyPARSE_DONT_IMPLY_DEDENT)) {
      p->tok->pendin = -p->tok->indent;
      p->tok->indent = 0;
    }
  } else {
    p->parsing_started = 1;
  }

  // Check if we are at the limit of the token array capacity and resize if
  // needed
  if ((p->fill == p->size) && (_resize_tokens_array(p) != 0)) {
    goto error;
  }

  Token *t = p->tokens[p->fill];
  return initialize_token(p, t, &new_token, type);
error:
  _PyToken_Free(&new_token);
  return -1;
}

static int // bool
_PyPegen_is_memoized(Parser *p, int type, void *pres) {
  if (p->mark == p->fill) {
    if (_PyPegen_fill_token(p) < 0) {
      p->error_indicator = 1;
      return -1;
    }
  }

  Token *t = p->tokens[p->mark];

  for (Memo *m = t->memo; m != NULL; m = m->next) {
    if (m->type == type) {
      p->mark = m->mark;
      *(void **)(pres) = m->node;
      return 1;
    }
  }
  return 0;
}

static int _PyPegen_lookahead_with_name(int positive, expr_ty(func)(Parser *),
                                        Parser *p) {
  int mark = p->mark;
  void *res = func(p);
  p->mark = mark;
  return (res != NULL) == positive;
}

static int _PyPegen_lookahead_with_string(int positive,
                                          expr_ty(func)(Parser *, const char *),
                                          Parser *p, const char *arg) {
  int mark = p->mark;
  void *res = func(p, arg);
  p->mark = mark;
  return (res != NULL) == positive;
}

static int _PyPegen_lookahead_with_int(int positive,
                                       Token *(func)(Parser *, int), Parser *p,
                                       int arg) {
  int mark = p->mark;
  void *res = func(p, arg);
  p->mark = mark;
  return (res != NULL) == positive;
}

static int _PyPegen_lookahead(int positive, void *(func)(Parser *), Parser *p) {
  int mark = p->mark;
  void *res = (void *)func(p);
  p->mark = mark;
  return (res != NULL) == positive;
}

static Token *_PyPegen_expect_token(Parser *p, int type) {
  if (p->mark == p->fill) {
    if (_PyPegen_fill_token(p) < 0) {
      p->error_indicator = 1;
      return NULL;
    }
  }
  Token *t = p->tokens[p->mark];
  if (t->type != type) {
    return NULL;
  }
  p->mark += 1;
  return t;
}

static Token *_PyPegen_expect_forced_token(Parser *p, int type,
                                           const char *expected) {

  if (p->error_indicator == 1) {
    return NULL;
  }

  if (p->mark == p->fill) {
    if (_PyPegen_fill_token(p) < 0) {
      p->error_indicator = 1;
      return NULL;
    }
  }
  Token *t = p->tokens[p->mark];
  if (t->type != type) {
    RAISE_SYNTAX_ERROR_KNOWN_LOCATION(t, "expected '%s'", expected);
    return NULL;
  }
  p->mark += 1;
  return t;
}

static Token *_PyPegen_get_last_nonnwhitespace_token(Parser *p) {
  assert(p->mark >= 0);
  Token *token = NULL;
  for (int m = p->mark - 1; m >= 0; m--) {
    token = p->tokens[m];
    if (token->type != ENDMARKER &&
        (token->type < NEWLINE || token->type > DEDENT)) {
      break;
    }
  }
  return token;
}

static PyObject *_PyPegen_new_identifier(Parser *p, const char *n) {
  PyObject *id = PyUnicode_DecodeUTF8(n, strlen(n), NULL);
  if (!id) {
    goto error;
  }
  /* PyUnicode_DecodeUTF8 should always return a ready string. */
  assert(PyUnicode_IS_READY(id));
  /* Check whether there are non-ASCII characters in the
     identifier; if so, normalize to NFKC. */
  if (!PyUnicode_IS_ASCII(id)) {
    PyObject *id2;
    if (!init_normalization(p)) {
      Py_DECREF(id);
      goto error;
    }
    PyObject *form = PyUnicode_InternFromString("NFKC");
    if (form == NULL) {
      Py_DECREF(id);
      goto error;
    }
    PyObject *args[2] = {form, id};
    id2 = _PyObject_FastCall(p->normalize, args, 2);
    Py_DECREF(id);
    Py_DECREF(form);
    if (!id2) {
      goto error;
    }
    if (!PyUnicode_Check(id2)) {
      PyErr_Format(PyExc_TypeError,
                   "unicodedata.normalize() must return a string, not "
                   "%.200s",
                   _PyType_Name(Py_TYPE(id2)));
      Py_DECREF(id2);
      goto error;
    }
    id = id2;
  }
  // PyInterpreterState *interp = _PyInterpreterState_GET();
  //_PyUnicode_InternImmortal(interp, &id);
  if (_PyArena_AddPyObject(p->arena, id) < 0) {
    Py_DECREF(id);
    goto error;
  }
  return id;

error:
  p->error_indicator = 1;
  return NULL;
}

static expr_ty _PyPegen_name_from_token(Parser *p, Token *t) {
  if (t == NULL) {
    return NULL;
  }
  const char *s = PyBytes_AsString(t->bytes);
  if (!s) {
    p->error_indicator = 1;
    return NULL;
  }
  PyObject *id = _PyPegen_new_identifier(p, s);
  if (id == NULL) {
    p->error_indicator = 1;
    return NULL;
  }
  return _PyAST_Name(id, Load, t->lineno, t->col_offset, t->end_lineno,
                     t->end_col_offset, p->arena);
}

static expr_ty _PyPegen_name_token(Parser *p) {
  Token *t = _PyPegen_expect_token(p, NAME);
  return _PyPegen_name_from_token(p, t);
}

static void *_PyPegen_string_token(Parser *p) {
  return _PyPegen_expect_token(p, STRING);
}

static expr_ty _PyPegen_expect_soft_keyword(Parser *p, const char *keyword) {
  if (p->mark == p->fill) {
    if (_PyPegen_fill_token(p) < 0) {
      p->error_indicator = 1;
      return NULL;
    }
  }
  Token *t = p->tokens[p->mark];
  if (t->type != NAME) {
    return NULL;
  }
  const char *s = PyBytes_AsString(t->bytes);
  if (!s) {
    p->error_indicator = 1;
    return NULL;
  }
  if (strcmp(s, keyword) != 0) {
    return NULL;
  }
  return _PyPegen_name_token(p);
}

static expr_ty _PyPegen_soft_keyword_token(Parser *p) {
  Token *t = _PyPegen_expect_token(p, NAME);
  if (t == NULL) {
    return NULL;
  }
  char *the_token;
  Py_ssize_t size;
  PyBytes_AsStringAndSize(t->bytes, &the_token, &size);
  for (char **keyword = p->soft_keywords; *keyword != NULL; keyword++) {
    if (strncmp(*keyword, the_token, size) == 0) {
      return _PyPegen_name_from_token(p, t);
    }
  }
  return NULL;
}

static PyObject *parsenumber_raw(const char *s) {
  const char *end;
  long x;
  double dx;
  Py_complex compl;
  int imflag;

  assert(s != NULL);
  errno = 0;
  end = s + strlen(s) - 1;
  imflag = *end == 'j' || *end == 'J';
  if (s[0] == '0') {
    x = (long)PyOS_strtoul(s, (char **)&end, 0);
    if (x < 0 && errno == 0) {
      return PyLong_FromString(s, (char **)0, 0);
    }
  } else {
    x = PyOS_strtol(s, (char **)&end, 0);
  }
  if (*end == '\0') {
    if (errno != 0) {
      return PyLong_FromString(s, (char **)0, 0);
    }
    return PyLong_FromLong(x);
  }
  /* XXX Huge floats may silently fail */
  if (imflag) {
    compl.real = 0.;
    compl.imag = PyOS_string_to_double(s, (char **)&end, NULL);
    if (compl.imag == -1.0 && PyErr_Occurred()) {
      return NULL;
    }
    return PyComplex_FromCComplex(compl);
  }
  dx = PyOS_string_to_double(s, NULL, NULL);
  if (dx == -1.0 && PyErr_Occurred()) {
    return NULL;
  }
  return PyFloat_FromDouble(dx);
}

static PyObject *parsenumber(const char *s) {
  char *dup;
  char *end;
  PyObject *res = NULL;

  assert(s != NULL);

  if (strchr(s, '_') == NULL) {
    return parsenumber_raw(s);
  }
  /* Create a duplicate without underscores. */
  dup = PyMem_Malloc(strlen(s) + 1);
  if (dup == NULL) {
    return PyErr_NoMemory();
  }
  end = dup;
  for (; *s; s++) {
    if (*s != '_') {
      *end++ = *s;
    }
  }
  *end = '\0';
  res = parsenumber_raw(dup);
  PyMem_Free(dup);
  return res;
}

static expr_ty _PyPegen_number_token(Parser *p) {
  Token *t = _PyPegen_expect_token(p, NUMBER);
  if (t == NULL) {
    return NULL;
  }

  const char *num_raw = PyBytes_AsString(t->bytes);
  if (num_raw == NULL) {
    p->error_indicator = 1;
    return NULL;
  }

  if (p->feature_version < 6 && strchr(num_raw, '_') != NULL) {
    p->error_indicator = 1;
    return RAISE_SYNTAX_ERROR(
        "Underscores in numeric literals are only supported "
        "in Python 3.6 and greater");
  }

  PyObject *c = parsenumber(num_raw);

  if (c == NULL) {
    p->error_indicator = 1;
    return NULL;
  }

  if (_PyArena_AddPyObject(p->arena, c) < 0) {
    Py_DECREF(c);
    p->error_indicator = 1;
    return NULL;
  }

  return _PyAST_Constant(c, NULL, t->lineno, t->col_offset, t->end_lineno,
                         t->end_col_offset, p->arena);
}

/* Check that the source for a single input statement really is a single
   statement by looking at what is left in the buffer after parsing.
   Trailing whitespace and comments are OK. */
static int // bool
bad_single_statement(Parser *p) {
  char *cur = p->tok->cur;
  char c = *cur;

  for (;;) {
    while (c == ' ' || c == '\t' || c == '\n' || c == '\014') {
      c = *++cur;
    }

    if (!c) {
      return 0;
    }

    if (c != '#') {
      return 1;
    }

    /* Suck up comment. */
    while (c && c != '\n') {
      c = *++cur;
    }
  }
}

// Parser API

static Parser *_PyPegen_Parser_New(struct tok_state *tok, int start_rule,
                                   int flags, int feature_version, int *errcode,
                                   PyArena *arena) {
  Parser *p = PyMem_Malloc(sizeof(Parser));
  if (p == NULL) {
    return (Parser *)PyErr_NoMemory();
  }
  assert(tok != NULL);
  tok->type_comments = (flags & PyPARSE_TYPE_COMMENTS) > 0;
  tok->async_hacks = (flags & PyPARSE_ASYNC_HACKS) > 0;
  p->tok = tok;
  p->keywords = NULL;
  p->n_keyword_lists = -1;
  p->soft_keywords = NULL;
  p->tokens = PyMem_Malloc(sizeof(Token *));
  if (!p->tokens) {
    PyMem_Free(p);
    return (Parser *)PyErr_NoMemory();
  }
  p->tokens[0] = PyMem_Calloc(1, sizeof(Token));
  if (!p->tokens[0]) {
    PyMem_Free(p->tokens);
    PyMem_Free(p);
    return (Parser *)PyErr_NoMemory();
  }
  if (!growable_comment_array_init(&p->type_ignore_comments, 10)) {
    PyMem_Free(p->tokens[0]);
    PyMem_Free(p->tokens);
    PyMem_Free(p);
    return (Parser *)PyErr_NoMemory();
  }

  PyObject *dummy = PyUnicode_FromString("");
  if (!dummy) {
    PyMem_Free(p->tokens[0]);
    PyMem_Free(p->tokens);
    PyMem_Free(p);
    return (Parser *)PyErr_NoMemory();
  }
  p->dummy_name.kind = Name_kind;
  p->dummy_name.v.Name.id = dummy;
  p->dummy_name.v.Name.ctx = Load,
  p->dummy_name.lineno = 1,
  p->dummy_name.col_offset = 0,
  p->dummy_name.end_lineno = 1,
  p->dummy_name.end_col_offset = 0,

  p->mark = 0;
  p->fill = 0;
  p->size = 1;

  p->errcode = errcode;
  p->arena = arena;
  p->start_rule = start_rule;
  p->parsing_started = 0;
  p->normalize = NULL;
  p->error_indicator = 0;

  p->starting_lineno = 0;
  p->starting_col_offset = 0;
  p->flags = flags;
  p->feature_version = feature_version;
  p->known_err_token = NULL;
  p->level = 0;
  p->call_invalid_rules = 0;
  return p;
}

static void _PyPegen_Parser_Free(Parser *p) {
  Py_XDECREF(p->normalize);
  Py_XDECREF(p->dummy_name.v.Name.id);
  for (int i = 0; i < p->size; i++) {
    PyMem_Free(p->tokens[i]);
  }
  PyMem_Free(p->tokens);
  growable_comment_array_deallocate(&p->type_ignore_comments);
  PyMem_Free(p);
}

static void reset_parser_state_for_error_pass(Parser *p) {
  for (int i = 0; i < p->fill; i++) {
    p->tokens[i]->memo = NULL;
  }
  p->mark = 0;
  p->call_invalid_rules = 1;
  // Don't try to get extra tokens in interactive mode when trying to
  // raise specialized errors in the second pass.
  p->tok->interactive_underflow = IUNDERFLOW_STOP;
}

static inline int _is_end_of_source(Parser *p) {
  int err = p->tok->done;
  return err == E_EOF || err == E_EOFS || err == E_EOLS;
}

static void *_PyPegen_run_parser(Parser *p) {
  void *res = _PyPegen_parse(p);
  assert(p->level == 0);
  if (res == NULL) {
    if ((p->flags & PyPARSE_ALLOW_INCOMPLETE_INPUT) && _is_end_of_source(p)) {
      PyErr_Clear();
      return RAISE_SYNTAX_ERROR("incomplete input");
    }
    if (PyErr_Occurred() && !PyErr_ExceptionMatches(PyExc_SyntaxError)) {
      return NULL;
    }
    // Make a second parser pass. In this pass we activate heavier and slower
    // checks to produce better error messages and more complete diagnostics.
    // Extra "invalid_*" rules will be active during parsing.
    Token *last_token = p->tokens[p->fill - 1];
    reset_parser_state_for_error_pass(p);
    _PyPegen_parse(p);

    // Set SyntaxErrors accordingly depending on the parser/tokenizer status at
    // the failure point.
    _Pypegen_set_syntax_error(p, last_token);
    return NULL;
  }

  if (p->start_rule == Py_single_input && bad_single_statement(p)) {
    p->tok->done = E_BADSINGLE; // This is not necessary for now, but might be
                                // in the future
    return RAISE_SYNTAX_ERROR(
        "multiple statements found while compiling a single statement");
  }

  return res;
}

static mod_ty _PyPegen_run_parser_from_string(const char *str,
                                              PyObject *filename_ob,
                                              PyArena *arena) {
  struct tok_state *tok = _PyTokenizer_FromString(str, 0, 0);
  if (tok == NULL) {
    if (PyErr_Occurred()) {
      _PyPegen_raise_tokenizer_init_error(filename_ob);
    }
    return NULL;
  }
  // This transfers the ownership to the tokenizer
  tok->filename = Py_NewRef(filename_ob);

  mod_ty result = NULL;
  Parser *p = _PyPegen_Parser_New(tok, Py_single_input, 0, 13, NULL, arena);
  if (p) {
    result = _PyPegen_run_parser(p);
    _PyPegen_Parser_Free(p);
  }

  _PyTokenizer_Free(tok);
  return result;
}
