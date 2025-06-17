/* Tokenizer implementation */

/* Error codes passed around between file input, tokenizer, parser and
   interpreter.  This is necessary so we can turn them into Python
   exceptions at a higher level.  Note that some errors have a
   slightly different meaning when passed from the tokenizer to the
   parser than when passed from the parser to the interpreter; e.g.
   the parser only returns E_EOF when it hits EOF immediately, and it
   never returns E_OK. */

#define E_OK 10            /* No error */
#define E_EOF 11           /* End Of File */
#define E_INTR 12          /* Interrupted */
#define E_TOKEN 13         /* Bad token */
#define E_SYNTAX 14        /* Syntax error */
#define E_NOMEM 15         /* Ran out of memory */
#define E_DONE 16          /* Parsing complete */
#define E_ERROR 17         /* Execution error */
#define E_TABSPACE 18      /* Inconsistent mixing of tabs and spaces */
#define E_OVERFLOW 19      /* Node had too many children */
#define E_TOODEEP 20       /* Too many indentation levels */
#define E_DEDENT 21        /* No matching outer block for dedent */
#define E_DECODE 22        /* Error in decoding into Unicode */
#define E_EOFS 23          /* EOF in triple-quoted string */
#define E_EOLS 24          /* EOL in single-quoted string */
#define E_LINECONT 25      /* Unexpected characters after a line continuation */
#define E_BADSINGLE 27     /* Ill-formed single statement input */
#define E_INTERACT_STOP 28 /* Interactive mode stopped tokenization */
#define E_COLUMNOVERFLOW 29 /* Column offset overflow */

/* Tokenizer interface */

#define MAXINDENT 100       /* Max indentation level */
#define MAXLEVEL 200        /* Max parentheses level */
#define MAXFSTRINGLEVEL 150 /* Max f-string nesting level */

enum decoding_state { STATE_INIT, STATE_SEEK_CODING, STATE_NORMAL };

enum interactive_underflow_t {
  /* Normal mode of operation: return a new token when asked in interactive mode
   */
  IUNDERFLOW_NORMAL,
  /* Forcefully return ENDMARKER when asked for a new token in interactive mode.
   * This can be used to prevent the tokenizer to prompt the user for new tokens
   */
  IUNDERFLOW_STOP,
};

struct token {
  int level;
  int lineno, col_offset, end_lineno, end_col_offset;
  const char *start, *end;
  PyObject *metadata;
};

enum tokenizer_mode_kind_t {
  TOK_REGULAR_MODE,
  TOK_FSTRING_MODE,
};

#define MAX_EXPR_NESTING 3

typedef struct _tokenizer_mode {
  enum tokenizer_mode_kind_t kind;

  int curly_bracket_depth;
  int curly_bracket_expr_start_depth;

  char f_string_quote;
  int f_string_quote_size;
  int f_string_raw;
  const char *f_string_start;
  const char *f_string_multi_line_start;
  int f_string_line_start;

  Py_ssize_t f_string_start_offset;
  Py_ssize_t f_string_multi_line_start_offset;

  Py_ssize_t last_expr_size;
  Py_ssize_t last_expr_end;
  char *last_expr_buffer;
  int f_string_debug;
  int in_format_spec;
} tokenizer_mode;

/* Tokenizer state */
struct tok_state {
  /* Input state; buf <= cur <= inp <= end */
  /* NB an entire line is held in the buffer */
  char *buf; /* Input buffer, or NULL; malloc'ed if fp != NULL or readline !=
                NULL */
  char *cur; /* Next character in buffer */
  char *inp; /* End of data in buffer */
  int fp_interactive;          /* If the file descriptor is interactive */
  char *interactive_src_start; /* The start of the source parsed so far in
                                  interactive mode */
  char *interactive_src_end;   /* The end of the source parsed so far in
                                  interactive mode */
  const char *end;             /* End of input buffer if buf != NULL */
  const char *start;           /* Start of current token if not NULL */
  int done; /* E_OK normally, E_EOF at EOF, otherwise error code */
  /* NB If done != E_OK, cur must be == inp!!! */
  FILE *fp;                /* Rest of input; NULL if tokenizing a string */
  int tabsize;             /* Tab spacing */
  int indent;              /* Current indentation index */
  int indstack[MAXINDENT]; /* Stack of indents */
  int atbol;               /* Nonzero if at begin of new line */
  int pendin;              /* Pending indents (if > 0) or dedents (if < 0) */
  const char *prompt, *nextprompt; /* For interactive prompting */
  int lineno;                      /* Current line number */
  int first_lineno;        /* First line of a single line or multi line string
                              expression (cf. issue 16806) */
  int starting_col_offset; /* The column offset at the beginning of a token */
  int col_offset;          /* Current col offset */
  int level;               /* () [] {} Parentheses nesting level */
                           /* Used to allow free continuations inside them */
  char parenstack[MAXLEVEL];
  int parenlinenostack[MAXLEVEL];
  int parencolstack[MAXLEVEL];
  PyObject *filename;
  /* Stuff for checking on different tab sizes */
  int altindstack[MAXINDENT]; /* Stack of alternate indents */
  /* Stuff for PEP 0263 */
  enum decoding_state decoding_state;
  int decoding_erred;           /* whether erred in decoding  */
  char *encoding;               /* Source encoding. */
  int cont_line;                /* whether we are in a continuation line. */
  const char *line_start;       /* pointer to start of current line */
  const char *multi_line_start; /* pointer to start of first line of
                                   a single line or multi line string
                                   expression (cf. issue 16806) */
  PyObject *decoding_readline;  /* open(...).readline */
  PyObject *decoding_buffer;
  PyObject *readline; /* readline() function */
  const char *enc;    /* Encoding for the current str. */
  char *str;   /* Source string being tokenized (if tokenizing from a string)*/
  char *input; /* Tokenizer's newline translated copy of the string. */

  int type_comments; /* Whether to look for type comments */

  /* async/await related fields (still needed depending on feature_version) */
  int async_hacks;      /* =1 if async/await aren't always keywords */
  int async_def;        /* =1 if tokens are inside an 'async def' body. */
  int async_def_indent; /* Indentation level of the outermost 'async def'. */
  int async_def_nl;     /* =1 if the outermost 'async def' had at least one
                           NEWLINE token after it. */
  /* How to proceed when asked for a new token in interactive mode */
  enum interactive_underflow_t interactive_underflow;
  int report_warnings;
  // TODO: Factor this into its own thing
  tokenizer_mode tok_mode_stack[MAXFSTRINGLEVEL];
  int tok_mode_stack_index;
  int tok_extra_tokens;
  int comment_newline;
  int implicit_newline;
};

#define tok_dump _Py_tok_dump

/* Alternate tab spacing */
#define ALTTABSIZE 1

#define is_potential_identifier_start(c)                                       \
  ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || (c >= 128))

#define is_potential_identifier_char(c)                                        \
  ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||                         \
   (c >= '0' && c <= '9') || c == '_' || (c >= 128))

/* Don't ever change this -- it would break the portability of Python code */
#define TABSIZE 8

#define MAKE_TOKEN(token_type)                                                 \
  token_setup(tok, token, token_type, p_start, p_end)
#define MAKE_TYPE_COMMENT_TOKEN(token_type, col_offset, end_col_offset)        \
  (type_comment_token_setup(tok, token, token_type, col_offset,                \
                            end_col_offset, p_start, p_end))
#define ADVANCE_LINENO()                                                       \
  tok->lineno++;                                                               \
  tok->col_offset = 0;

#define INSIDE_FSTRING(tok) (tok->tok_mode_stack_index > 0)
#define INSIDE_FSTRING_EXPR(tok) (tok->curly_bracket_expr_start_depth >= 0)
#ifdef Py_DEBUG
static inline tokenizer_mode *TOK_GET_MODE(struct tok_state *tok) {
  assert(tok->tok_mode_stack_index >= 0);
  assert(tok->tok_mode_stack_index < MAXFSTRINGLEVEL);
  return &(tok->tok_mode_stack[tok->tok_mode_stack_index]);
}
static inline tokenizer_mode *TOK_NEXT_MODE(struct tok_state *tok) {
  assert(tok->tok_mode_stack_index >= 0);
  assert(tok->tok_mode_stack_index + 1 < MAXFSTRINGLEVEL);
  return &(tok->tok_mode_stack[++tok->tok_mode_stack_index]);
}
#else
#define TOK_GET_MODE(tok) (&(tok->tok_mode_stack[tok->tok_mode_stack_index]))
#define TOK_NEXT_MODE(tok) (&(tok->tok_mode_stack[++tok->tok_mode_stack_index]))
#endif

/* Forward */
static struct tok_state *tok_new(void);
static int tok_nextc(struct tok_state *tok);
static void tok_backup(struct tok_state *tok, int c);
static int syntaxerror(struct tok_state *tok, const char *format, ...);

/* Spaces in this constant are treated as "zero or more spaces or tabs" when
   tokenizing. */
static const char *type_comment_prefix = "# type: ";

/* Create and initialize a new tok_state structure */

static struct tok_state *tok_new(void) {
  struct tok_state *tok =
      (struct tok_state *)PyMem_Calloc(1, sizeof(struct tok_state));
  if (tok == NULL)
    return NULL;
  tok->buf = tok->cur = tok->inp = NULL;
  tok->fp_interactive = 0;
  tok->interactive_src_start = NULL;
  tok->interactive_src_end = NULL;
  tok->start = NULL;
  tok->end = NULL;
  tok->done = E_OK;
  tok->fp = NULL;
  tok->input = NULL;
  tok->tabsize = TABSIZE;
  tok->indent = 0;
  tok->indstack[0] = 0;
  tok->atbol = 1;
  tok->pendin = 0;
  tok->prompt = tok->nextprompt = NULL;
  tok->lineno = 0;
  tok->starting_col_offset = -1;
  tok->col_offset = -1;
  tok->level = 0;
  tok->altindstack[0] = 0;
  tok->decoding_state = STATE_INIT;
  tok->decoding_erred = 0;
  tok->enc = NULL;
  tok->encoding = NULL;
  tok->cont_line = 0;
  tok->filename = NULL;
  tok->decoding_readline = NULL;
  tok->decoding_buffer = NULL;
  tok->readline = NULL;
  tok->type_comments = 0;
  tok->async_hacks = 0;
  tok->async_def = 0;
  tok->async_def_indent = 0;
  tok->async_def_nl = 0;
  tok->interactive_underflow = IUNDERFLOW_NORMAL;
  tok->str = NULL;
  tok->report_warnings = 1;
  tok->tok_extra_tokens = 0;
  tok->comment_newline = 0;
  tok->implicit_newline = 0;
  tok->tok_mode_stack[0] = (tokenizer_mode){.kind = TOK_REGULAR_MODE,
                                            .f_string_quote = '\0',
                                            .f_string_quote_size = 0,
                                            .f_string_debug = 0};
  tok->tok_mode_stack_index = 0;
  return tok;
}

/* Free a tok_state structure */

static void free_fstring_expressions(struct tok_state *tok) {
  int index;
  tokenizer_mode *mode;

  for (index = tok->tok_mode_stack_index; index >= 0; --index) {
    mode = &(tok->tok_mode_stack[index]);
    if (mode->last_expr_buffer != NULL) {
      PyMem_Free(mode->last_expr_buffer);
      mode->last_expr_buffer = NULL;
      mode->last_expr_size = 0;
      mode->last_expr_end = -1;
      mode->in_format_spec = 0;
    }
  }
}

static void _PyTokenizer_Free(struct tok_state *tok) {
  if (tok->encoding != NULL) {
    PyMem_Free(tok->encoding);
  }
  Py_XDECREF(tok->decoding_readline);
  Py_XDECREF(tok->decoding_buffer);
  Py_XDECREF(tok->readline);
  Py_XDECREF(tok->filename);
  if ((tok->readline != NULL || tok->fp != NULL) && tok->buf != NULL) {
    PyMem_Free(tok->buf);
  }
  if (tok->input) {
    PyMem_Free(tok->input);
  }
  if (tok->interactive_src_start != NULL) {
    PyMem_Free(tok->interactive_src_start);
  }
  free_fstring_expressions(tok);
  PyMem_Free(tok);
}

static char *new_string(const char *s, Py_ssize_t len, struct tok_state *tok) {
  char *result = (char *)PyMem_Malloc(len + 1);
  if (!result) {
    tok->done = E_NOMEM;
    return NULL;
  }
  memcpy(result, s, len);
  result[len] = '\0';
  return result;
}

static char *error_ret(struct tok_state *tok) /* XXX */
{
  tok->decoding_erred = 1;
  if ((tok->fp != NULL || tok->readline != NULL) &&
      tok->buf != NULL) { /* see _PyTokenizer_Free */
    PyMem_Free(tok->buf);
  }
  tok->buf = tok->cur = tok->inp = NULL;
  tok->start = NULL;
  tok->end = NULL;
  tok->done = E_DECODE;
  return NULL; /* as if it were EOF */
}

static const char *get_normal_name(const char *s) /* for utf-8 and latin-1 */
{
  char buf[13];
  int i;
  for (i = 0; i < 12; i++) {
    int c = s[i];
    if (c == '\0')
      break;
    else if (c == '_')
      buf[i] = '-';
    else
      buf[i] = tolower(c);
  }
  buf[i] = '\0';
  if (strcmp(buf, "utf-8") == 0 || strncmp(buf, "utf-8-", 6) == 0)
    return "utf-8";
  else if (strcmp(buf, "latin-1") == 0 || strcmp(buf, "iso-8859-1") == 0 ||
           strcmp(buf, "iso-latin-1") == 0 ||
           strncmp(buf, "latin-1-", 8) == 0 ||
           strncmp(buf, "iso-8859-1-", 11) == 0 ||
           strncmp(buf, "iso-latin-1-", 12) == 0)
    return "iso-8859-1";
  else
    return s;
}

/* Return the coding spec in S, or NULL if none is found.  */

static int get_coding_spec(const char *s, char **spec, Py_ssize_t size,
                           struct tok_state *tok) {
  Py_ssize_t i;
  *spec = NULL;
  /* Coding spec must be in a comment, and that comment must be
   * the only statement on the source code line. */
  for (i = 0; i < size - 6; i++) {
    if (s[i] == '#')
      break;
    if (s[i] != ' ' && s[i] != '\t' && s[i] != '\014')
      return 1;
  }
  for (; i < size - 6; i++) { /* XXX inefficient search */
    const char *t = s + i;
    if (memcmp(t, "coding", 6) == 0) {
      const char *begin = NULL;
      t += 6;
      if (t[0] != ':' && t[0] != '=')
        continue;
      do {
        t++;
      } while (t[0] == ' ' || t[0] == '\t');

      begin = t;
      while (Py_ISALNUM(t[0]) || t[0] == '-' || t[0] == '_' || t[0] == '.')
        t++;

      if (begin < t) {
        char *r = new_string(begin, t - begin, tok);
        const char *q;
        if (!r)
          return 0;
        q = get_normal_name(r);
        if (r != q) {
          PyMem_Free(r);
          r = new_string(q, strlen(q), tok);
          if (!r)
            return 0;
        }
        *spec = r;
        break;
      }
    }
  }
  return 1;
}

/* Check whether the line contains a coding spec. If it does,
   invoke the set_readline function for the new encoding.
   This function receives the tok_state and the new encoding.
   Return 1 on success, 0 on failure.  */

static int
check_coding_spec(const char *line, Py_ssize_t size, struct tok_state *tok,
                  int set_readline(struct tok_state *, const char *)) {
  char *cs;
  if (tok->cont_line) {
    /* It's a continuation line, so it can't be a coding spec. */
    tok->decoding_state = STATE_NORMAL;
    return 1;
  }
  if (!get_coding_spec(line, &cs, size, tok)) {
    return 0;
  }
  if (!cs) {
    Py_ssize_t i;
    for (i = 0; i < size; i++) {
      if (line[i] == '#' || line[i] == '\n' || line[i] == '\r')
        break;
      if (line[i] != ' ' && line[i] != '\t' && line[i] != '\014') {
        /* Stop checking coding spec after a line containing
         * anything except a comment. */
        tok->decoding_state = STATE_NORMAL;
        break;
      }
    }
    return 1;
  }
  tok->decoding_state = STATE_NORMAL;
  if (tok->encoding == NULL) {
    assert(tok->decoding_readline == NULL);
    if (strcmp(cs, "utf-8") != 0 && !set_readline(tok, cs)) {
      error_ret(tok);
      PyErr_Format(PyExc_SyntaxError, "encoding problem: %s", cs);
      PyMem_Free(cs);
      return 0;
    }
    tok->encoding = cs;
  } else { /* then, compare cs with BOM */
    if (strcmp(tok->encoding, cs) != 0) {
      error_ret(tok);
      PyErr_Format(PyExc_SyntaxError, "encoding problem: %s with BOM", cs);
      PyMem_Free(cs);
      return 0;
    }
    PyMem_Free(cs);
  }
  return 1;
}

/* See whether the file starts with a BOM. If it does,
   invoke the set_readline function with the new encoding.
   Return 1 on success, 0 on failure.  */

static int check_bom(int get_char(struct tok_state *),
                     void unget_char(int, struct tok_state *),
                     struct tok_state *tok) {
  int ch1, ch2, ch3;
  ch1 = get_char(tok);
  tok->decoding_state = STATE_SEEK_CODING;
  if (ch1 == EOF) {
    return 1;
  } else if (ch1 == 0xEF) {
    ch2 = get_char(tok);
    if (ch2 != 0xBB) {
      unget_char(ch2, tok);
      unget_char(ch1, tok);
      return 1;
    }
    ch3 = get_char(tok);
    if (ch3 != 0xBF) {
      unget_char(ch3, tok);
      unget_char(ch2, tok);
      unget_char(ch1, tok);
      return 1;
    }
  } else {
    unget_char(ch1, tok);
    return 1;
  }
  if (tok->encoding != NULL)
    PyMem_Free(tok->encoding);
  tok->encoding = new_string("utf-8", 5, tok);
  if (!tok->encoding)
    return 0;
  /* No need to set_readline: input is already utf-8 */
  return 1;
}

static int set_fstring_expr(struct tok_state *tok, struct token *token,
                            char c) {
  assert(token != NULL);
  assert(c == '}' || c == ':' || c == '!');
  tokenizer_mode *tok_mode = TOK_GET_MODE(tok);

  if (!tok_mode->f_string_debug || token->metadata) {
    return 0;
  }

  PyObject *res = NULL;

  // Check if there is a # character in the expression
  int hash_detected = 0;
  for (Py_ssize_t i = 0; i < tok_mode->last_expr_size - tok_mode->last_expr_end;
       i++) {
    if (tok_mode->last_expr_buffer[i] == '#') {
      hash_detected = 1;
      break;
    }
  }

  if (hash_detected) {
    Py_ssize_t input_length =
        tok_mode->last_expr_size - tok_mode->last_expr_end;
    char *result = (char *)PyObject_Malloc((input_length + 1) * sizeof(char));
    if (!result) {
      return -1;
    }

    Py_ssize_t i = 0;
    Py_ssize_t j = 0;

    for (i = 0, j = 0; i < input_length; i++) {
      if (tok_mode->last_expr_buffer[i] == '#') {
        // Skip characters until newline or end of string
        while (tok_mode->last_expr_buffer[i] != '\0' && i < input_length) {
          if (tok_mode->last_expr_buffer[i] == '\n') {
            result[j++] = tok_mode->last_expr_buffer[i];
            break;
          }
          i++;
        }
      } else {
        result[j++] = tok_mode->last_expr_buffer[i];
      }
    }

    result[j] = '\0'; // Null-terminate the result string
    res = PyUnicode_DecodeUTF8(result, j, NULL);
    PyObject_Free(result);
  } else {
    res = PyUnicode_DecodeUTF8(
        tok_mode->last_expr_buffer,
        tok_mode->last_expr_size - tok_mode->last_expr_end, NULL);
  }

  if (!res) {
    return -1;
  }
  token->metadata = res;
  return 0;
}

static int update_fstring_expr(struct tok_state *tok, char cur) {
  assert(tok->cur != NULL);

  Py_ssize_t size = strlen(tok->cur);
  tokenizer_mode *tok_mode = TOK_GET_MODE(tok);

  switch (cur) {
  case 0:
    if (!tok_mode->last_expr_buffer || tok_mode->last_expr_end >= 0) {
      return 1;
    }
    char *new_buffer = PyMem_Realloc(tok_mode->last_expr_buffer,
                                     tok_mode->last_expr_size + size);
    if (new_buffer == NULL) {
      PyMem_Free(tok_mode->last_expr_buffer);
      goto error;
    }
    tok_mode->last_expr_buffer = new_buffer;
    strncpy(tok_mode->last_expr_buffer + tok_mode->last_expr_size, tok->cur,
            size);
    tok_mode->last_expr_size += size;
    break;
  case '{':
    if (tok_mode->last_expr_buffer != NULL) {
      PyMem_Free(tok_mode->last_expr_buffer);
    }
    tok_mode->last_expr_buffer = PyMem_Malloc(size);
    if (tok_mode->last_expr_buffer == NULL) {
      goto error;
    }
    tok_mode->last_expr_size = size;
    tok_mode->last_expr_end = -1;
    strncpy(tok_mode->last_expr_buffer, tok->cur, size);
    break;
  case '}':
  case '!':
  case ':':
    tok_mode->last_expr_end = strlen(tok->start);
    break;
  default:
    Py_UNREACHABLE();
  }
  return 1;
error:
  tok->done = E_NOMEM;
  return 0;
}

static inline int contains_null_bytes(const char *str, size_t size) {
  return memchr(str, 0, size) != NULL;
}

/* Fetch a byte from TOK, using the string buffer. */

static int buf_getc(struct tok_state *tok) { return Py_CHARMASK(*tok->str++); }

/* Unfetch a byte from TOK, using the string buffer. */

static void buf_ungetc(int c, struct tok_state *tok) {
  tok->str--;
  assert(Py_CHARMASK(*tok->str) ==
         c); /* tok->cur may point to read-only segment */
}

/* Set the readline function for TOK to ENC. For the string-based
   tokenizer, this means to just record the encoding. */

static int buf_setreadl(struct tok_state *tok, const char *enc) {
  tok->enc = enc;
  return 1;
}

/* Return a UTF-8 encoding Python string object from the
   C byte string STR, which is encoded with ENC. */

static PyObject *translate_into_utf8(const char *str, const char *enc) {
  PyObject *utf8;
  PyObject *buf = PyUnicode_Decode(str, strlen(str), enc, NULL);
  if (buf == NULL)
    return NULL;
  utf8 = PyUnicode_AsUTF8String(buf);
  Py_DECREF(buf);
  return utf8;
}

static char *translate_newlines(const char *s, int exec_input,
                                int preserve_crlf, struct tok_state *tok) {
  int skip_next_lf = 0;
  size_t needed_length = strlen(s) + 2, final_length;
  char *buf, *current;
  char c = '\0';
  buf = PyMem_Malloc(needed_length);
  if (buf == NULL) {
    tok->done = E_NOMEM;
    return NULL;
  }
  for (current = buf; *s; s++, current++) {
    c = *s;
    if (skip_next_lf) {
      skip_next_lf = 0;
      if (c == '\n') {
        c = *++s;
        if (!c)
          break;
      }
    }
    if (!preserve_crlf && c == '\r') {
      skip_next_lf = 1;
      c = '\n';
    }
    *current = c;
  }
  /* If this is exec input, add a newline to the end of the string if
     there isn't one already. */
  if (exec_input && c != '\n' && c != '\0') {
    *current = '\n';
    current++;
  }
  *current = '\0';
  final_length = current - buf + 1;
  if (final_length < needed_length && final_length) {
    /* should never fail */
    char *result = PyMem_Realloc(buf, final_length);
    if (result == NULL) {
      PyMem_Free(buf);
    }
    buf = result;
  }
  return buf;
}

/* Decode a byte string STR for use as the buffer of TOK.
   Look for encoding declarations inside STR, and record them
   inside TOK.  */

static char *decode_str(const char *input, int single, struct tok_state *tok,
                        int preserve_crlf) {
  PyObject *utf8 = NULL;
  char *str;
  const char *s;
  const char *newl[2] = {NULL, NULL};
  int lineno = 0;
  tok->input = str = translate_newlines(input, single, preserve_crlf, tok);
  if (str == NULL)
    return NULL;
  tok->enc = NULL;
  tok->str = str;
  if (!check_bom(buf_getc, buf_ungetc, tok))
    return error_ret(tok);
  str = tok->str; /* string after BOM if any */
  assert(str);
  if (tok->enc != NULL) {
    utf8 = translate_into_utf8(str, tok->enc);
    if (utf8 == NULL)
      return error_ret(tok);
    str = PyBytes_AsString(utf8);
  }
  for (s = str;; s++) {
    if (*s == '\0')
      break;
    else if (*s == '\n') {
      assert(lineno < 2);
      newl[lineno] = s;
      lineno++;
      if (lineno == 2)
        break;
    }
  }
  tok->enc = NULL;
  /* need to check line 1 and 2 separately since check_coding_spec
     assumes a single line as input */
  if (newl[0]) {
    if (!check_coding_spec(str, newl[0] - str, tok, buf_setreadl)) {
      return NULL;
    }
    if (tok->enc == NULL && tok->decoding_state != STATE_NORMAL && newl[1]) {
      if (!check_coding_spec(newl[0] + 1, newl[1] - newl[0], tok, buf_setreadl))
        return NULL;
    }
  }
  if (tok->enc != NULL) {
    assert(utf8 == NULL);
    utf8 = translate_into_utf8(str, tok->enc);
    if (utf8 == NULL)
      return error_ret(tok);
    str = PyBytes_AS_STRING(utf8);
  }
  assert(tok->decoding_buffer == NULL);
  tok->decoding_buffer = utf8; /* CAUTION */
  return str;
}

/* Set up tokenizer for string */

static struct tok_state *
_PyTokenizer_FromString(const char *str, int exec_input, int preserve_crlf) {
  struct tok_state *tok = tok_new();
  char *decoded;

  if (tok == NULL)
    return NULL;
  decoded = decode_str(str, exec_input, tok, preserve_crlf);
  if (decoded == NULL) {
    _PyTokenizer_Free(tok);
    return NULL;
  }

  tok->buf = tok->cur = tok->inp = decoded;
  tok->end = decoded;
  return tok;
}

static void _PyToken_Free(struct token *token) { Py_XDECREF(token->metadata); }

static void _PyToken_Init(struct token *token) { token->metadata = NULL; }

static int tok_underflow_string(struct tok_state *tok) {
  char *end = strchr(tok->inp, '\n');
  if (end != NULL) {
    end++;
  } else {
    end = strchr(tok->inp, '\0');
    if (end == tok->inp) {
      tok->done = E_EOF;
      return 0;
    }
  }
  if (tok->start == NULL) {
    tok->buf = tok->cur;
  }
  tok->line_start = tok->cur;
  ADVANCE_LINENO();
  tok->inp = end;
  return 1;
}

/* Get next char, updating state; error code goes into tok->done */

static int tok_nextc(struct tok_state *tok) {
  int rc;
  for (;;) {
    if (tok->cur != tok->inp) {
      if ((unsigned int)tok->col_offset >= (unsigned int)INT_MAX) {
        tok->done = 29; // E_COLUMNOVERFLOW;
        return EOF;
      }
      tok->col_offset++;
      return Py_CHARMASK(*tok->cur++); /* Fast path */
    }
    if (tok->done != E_OK) {
      return EOF;
    }
    if (tok->fp == NULL) {
      rc = tok_underflow_string(tok);
    }
#if defined(Py_DEBUG)
    if (tok->debug) {
      fprintf(stderr, "line[%d] = ", tok->lineno);
      print_escape(stderr, tok->cur, tok->inp - tok->cur);
      fprintf(stderr, "  tok->done = %d\n", tok->done);
    }
#endif
    if (!rc) {
      tok->cur = tok->inp;
      return EOF;
    }
    tok->line_start = tok->cur;

    if (contains_null_bytes(tok->line_start, tok->inp - tok->line_start)) {
      syntaxerror(tok, "source code cannot contain null bytes");
      tok->cur = tok->inp;
      return EOF;
    }
  }
  Py_UNREACHABLE();
}

/* Back-up one character */

static void tok_backup(struct tok_state *tok, int c) {
  if (c != EOF) {
    if (--tok->cur < tok->buf) {
      Py_FatalError("tokenizer beginning of buffer");
    }
    if ((int)(unsigned char)*tok->cur != Py_CHARMASK(c)) {
      Py_FatalError("tok_backup: wrong character");
    }
    tok->col_offset--;
  }
}

static int _syntaxerror_range(struct tok_state *tok, const char *format,
                              int col_offset, int end_col_offset,
                              va_list vargs) {
  // In release builds, we don't want to overwrite a previous error, but in
  // debug builds we want to fail if we are not doing it so we can fix it.
  assert(tok->done != E_ERROR);
  if (tok->done == E_ERROR) {
    return ERRORTOKEN;
  }
  PyObject *errmsg, *errtext, *args;
  errmsg = PyUnicode_FromFormatV(format, vargs);
  if (!errmsg) {
    goto error;
  }

  errtext = PyUnicode_DecodeUTF8(tok->line_start, tok->cur - tok->line_start,
                                 "replace");
  if (!errtext) {
    goto error;
  }

  if (col_offset == -1) {
    col_offset = (int)PyUnicode_GET_LENGTH(errtext);
  }
  if (end_col_offset == -1) {
    end_col_offset = col_offset;
  }

  Py_ssize_t line_len = strcspn(tok->line_start, "\n");
  if (line_len != tok->cur - tok->line_start) {
    Py_DECREF(errtext);
    errtext = PyUnicode_DecodeUTF8(tok->line_start, line_len, "replace");
  }
  if (!errtext) {
    goto error;
  }

  args = Py_BuildValue("(O(OiiNii))", errmsg, tok->filename, tok->lineno,
                       col_offset, errtext, tok->lineno, end_col_offset);
  if (args) {
    PyErr_SetObject(PyExc_SyntaxError, args);
    Py_DECREF(args);
  }

error:
  Py_XDECREF(errmsg);
  tok->done = E_ERROR;
  return ERRORTOKEN;
}

static int syntaxerror(struct tok_state *tok, const char *format, ...) {
  // This errors are cleaned on startup. Todo: Fix it.
  va_list vargs;
  va_start(vargs, format);
  int ret = _syntaxerror_range(tok, format, -1, -1, vargs);
  va_end(vargs);
  return ret;
}

static int syntaxerror_known_range(struct tok_state *tok, int col_offset,
                                   int end_col_offset, const char *format,
                                   ...) {
  va_list vargs;
  va_start(vargs, format);
  int ret = _syntaxerror_range(tok, format, col_offset, end_col_offset, vargs);
  va_end(vargs);
  return ret;
}

static int indenterror(struct tok_state *tok) {
  tok->done = E_TABSPACE;
  tok->cur = tok->inp;
  return ERRORTOKEN;
}

static int parser_warn(struct tok_state *tok, PyObject *category,
                       const char *format, ...) {
  if (!tok->report_warnings) {
    return 0;
  }

  PyObject *errmsg;
  va_list vargs;
  va_start(vargs, format);
  errmsg = PyUnicode_FromFormatV(format, vargs);
  va_end(vargs);
  if (!errmsg) {
    goto error;
  }

  if (PyErr_WarnExplicitObject(category, errmsg, tok->filename, tok->lineno,
                               NULL, NULL) < 0) {
    if (PyErr_ExceptionMatches(category)) {
      /* Replace the DeprecationWarning exception with a SyntaxError
         to get a more accurate error report */
      PyErr_Clear();
      syntaxerror(tok, "%U", errmsg);
    }
    goto error;
  }
  Py_DECREF(errmsg);
  return 0;

error:
  Py_XDECREF(errmsg);
  tok->done = E_ERROR;
  return -1;
}

static int warn_invalid_escape_sequence0(struct tok_state *tok,
                                         int first_invalid_escape_char) {
  if (!tok->report_warnings) {
    return 0;
  }

  PyObject *msg = PyUnicode_FromFormat("invalid escape sequence '\\%c'",
                                       (char)first_invalid_escape_char);

  if (msg == NULL) {
    return -1;
  }

  if (PyErr_WarnExplicitObject(PyExc_SyntaxWarning, msg, tok->filename,
                               tok->lineno, NULL, NULL) < 0) {
    Py_DECREF(msg);

    if (PyErr_ExceptionMatches(PyExc_SyntaxWarning)) {
      /* Replace the SyntaxWarning exception with a SyntaxError
         to get a more accurate error report */
      PyErr_Clear();
      return syntaxerror(tok, "invalid escape sequence '\\%c'",
                         (char)first_invalid_escape_char);
    }

    return -1;
  }

  Py_DECREF(msg);
  return 0;
}

static int lookahead(struct tok_state *tok, const char *test) {
  const char *s = test;
  int res = 0;
  while (1) {
    int c = tok_nextc(tok);
    if (*s == 0) {
      res = !is_potential_identifier_char(c);
    } else if (c == *s) {
      s++;
      continue;
    }

    tok_backup(tok, c);
    while (s != test) {
      tok_backup(tok, *--s);
    }
    return res;
  }
}

static int verify_end_of_number(struct tok_state *tok, int c,
                                const char *kind) {
  if (tok->tok_extra_tokens) {
    // When we are parsing extra tokens, we don't want to emit warnings
    // about invalid literals, because we want to be a bit more liberal.
    return 1;
  }
  /* Emit a deprecation warning only if the numeric literal is immediately
   * followed by one of keywords which can occur after a numeric literal
   * in valid code: "and", "else", "for", "if", "in", "is" and "or".
   * It allows to gradually deprecate existing valid code without adding
   * warning before error in most cases of invalid numeric literal (which
   * would be confusing and break existing tests).
   * Raise a syntax error with slightly better message than plain
   * "invalid syntax" if the numeric literal is immediately followed by
   * other keyword or identifier.
   */
  int r = 0;
  if (c == 'a') {
    r = lookahead(tok, "nd");
  } else if (c == 'e') {
    r = lookahead(tok, "lse");
  } else if (c == 'f') {
    r = lookahead(tok, "or");
  } else if (c == 'i') {
    int c2 = tok_nextc(tok);
    if (c2 == 'f' || c2 == 'n' || c2 == 's') {
      r = 1;
    }
    tok_backup(tok, c2);
  } else if (c == 'o') {
    r = lookahead(tok, "r");
  } else if (c == 'n') {
    r = lookahead(tok, "ot");
  }
  if (r) {
    tok_backup(tok, c);
    if (parser_warn(tok, PyExc_SyntaxWarning, "invalid %s literal", kind)) {
      return 0;
    }
    tok_nextc(tok);
  } else /* In future releases, only error will remain. */
    if (c < 128 && is_potential_identifier_char(c)) {
      tok_backup(tok, c);
      syntaxerror(tok, "invalid %s literal", kind);
      return 0;
    }
  return 1;
}

/* Verify that the identifier follows PEP 3131.
   All identifier strings are guaranteed to be "ready" unicode objects.
 */
static int verify_identifier(struct tok_state *tok) {
  if (tok->tok_extra_tokens) {
    return 1;
  }
  PyObject *s;
  if (tok->decoding_erred)
    return 0;
  s = PyUnicode_DecodeUTF8(tok->start, tok->cur - tok->start, NULL);
  if (s == NULL) {
    if (PyErr_ExceptionMatches(PyExc_UnicodeDecodeError)) {
      tok->done = E_DECODE;
    } else {
      tok->done = E_ERROR;
    }
    return 0;
  }
  Py_ssize_t invalid = _PyUnicode_ScanIdentifier(s);
  if (invalid < 0) {
    Py_DECREF(s);
    tok->done = E_ERROR;
    return 0;
  }
  assert(PyUnicode_GET_LENGTH(s) > 0);
  if (invalid < PyUnicode_GET_LENGTH(s)) {
    Py_UCS4 ch = PyUnicode_READ_CHAR(s, invalid);
    if (invalid + 1 < PyUnicode_GET_LENGTH(s)) {
      /* Determine the offset in UTF-8 encoded input */
      Py_SETREF(s, PyUnicode_Substring(s, 0, invalid + 1));
      if (s != NULL) {
        Py_SETREF(s, PyUnicode_AsUTF8String(s));
      }
      if (s == NULL) {
        tok->done = E_ERROR;
        return 0;
      }
      tok->cur = (char *)tok->start + PyBytes_GET_SIZE(s);
    }
    Py_DECREF(s);
    if (Py_UNICODE_ISPRINTABLE(ch)) {
      syntaxerror(tok, "invalid character '%c' (U+%04X)", ch, ch);
    } else {
      syntaxerror(tok, "invalid non-printable character U+%04X", ch);
    }
    return 0;
  }
  Py_DECREF(s);
  return 1;
}

static int tok_decimal_tail(struct tok_state *tok) {
  int c;

  while (1) {
    do {
      c = tok_nextc(tok);
    } while (isdigit(c));
    if (c != '_') {
      break;
    }
    c = tok_nextc(tok);
    if (!isdigit(c)) {
      tok_backup(tok, c);
      syntaxerror(tok, "invalid decimal literal");
      return 0;
    }
  }
  return c;
}

static inline int tok_continuation_line(struct tok_state *tok) {
  int c = tok_nextc(tok);
  if (c == '\r') {
    c = tok_nextc(tok);
  }
  if (c != '\n') {
    tok->done = E_LINECONT;
    return -1;
  }
  c = tok_nextc(tok);
  if (c == EOF) {
    tok->done = E_EOF;
    tok->cur = tok->inp;
    return -1;
  } else {
    tok_backup(tok, c);
  }
  return c;
}

static int type_comment_token_setup(struct tok_state *tok, struct token *token,
                                    int type, int col_offset,
                                    int end_col_offset, const char *start,
                                    const char *end) {
  token->level = tok->level;
  token->lineno = token->end_lineno = tok->lineno;
  token->col_offset = col_offset;
  token->end_col_offset = end_col_offset;
  token->start = start;
  token->end = end;
  return type;
}

static int token_setup(struct tok_state *tok, struct token *token, int type,
                       const char *start, const char *end) {
  assert((start == NULL && end == NULL) || (start != NULL && end != NULL));
  token->level = tok->level;
  if (ISSTRINGLIT(type)) {
    token->lineno = tok->first_lineno;
  } else {
    token->lineno = tok->lineno;
  }
  token->end_lineno = tok->lineno;
  token->col_offset = token->end_col_offset = -1;
  token->start = start;
  token->end = end;

  if (start != NULL && end != NULL) {
    token->col_offset = tok->starting_col_offset;
    token->end_col_offset = tok->col_offset;
  }
  return type;
}

static int tok_get_normal_mode(struct tok_state *tok,
                               tokenizer_mode *current_tok,
                               struct token *token) {
  int c;
  int blankline, nonascii;

  const char *p_start = NULL;
  const char *p_end = NULL;
nextline:
  tok->start = NULL;
  tok->starting_col_offset = -1;
  blankline = 0;

  /* Get indentation level */
  if (tok->atbol) {
    int col = 0;
    int altcol = 0;
    tok->atbol = 0;
    int cont_line_col = 0;
    for (;;) {
      c = tok_nextc(tok);
      if (c == ' ') {
        col++, altcol++;
      } else if (c == '\t') {
        col = (col / tok->tabsize + 1) * tok->tabsize;
        altcol = (altcol / ALTTABSIZE + 1) * ALTTABSIZE;
      } else if (c == '\014') { /* Control-L (formfeed) */
        col = altcol = 0;       /* For Emacs users */
      } else if (c == '\\') {
        // Indentation cannot be split over multiple physical lines
        // using backslashes. This means that if we found a backslash
        // preceded by whitespace, **the first one we find** determines
        // the level of indentation of whatever comes next.
        cont_line_col = cont_line_col ? cont_line_col : col;
        if ((c = tok_continuation_line(tok)) == -1) {
          return MAKE_TOKEN(ERRORTOKEN);
        }
      } else {
        break;
      }
    }
    tok_backup(tok, c);
    if (c == '#' || c == '\n' || c == '\r') {
      /* Lines with only whitespace and/or comments
         shouldn't affect the indentation and are
         not passed to the parser as NEWLINE tokens,
         except *totally* empty lines in interactive
         mode, which signal the end of a command group. */
      if (col == 0 && c == '\n' && tok->prompt != NULL) {
        blankline = 0; /* Let it through */
      } else if (tok->prompt != NULL && tok->lineno == 1) {
        /* In interactive mode, if the first line contains
           only spaces and/or a comment, let it through. */
        blankline = 0;
        col = altcol = 0;
      } else {
        blankline = 1; /* Ignore completely */
      }
      /* We can't jump back right here since we still
         may need to skip to the end of a comment */
    }
    if (!blankline && tok->level == 0) {
      col = cont_line_col ? cont_line_col : col;
      altcol = cont_line_col ? cont_line_col : altcol;
      if (col == tok->indstack[tok->indent]) {
        /* No change */
        if (altcol != tok->altindstack[tok->indent]) {
          return MAKE_TOKEN(indenterror(tok));
        }
      } else if (col > tok->indstack[tok->indent]) {
        /* Indent -- always one */
        if (tok->indent + 1 >= MAXINDENT) {
          tok->done = E_TOODEEP;
          tok->cur = tok->inp;
          return MAKE_TOKEN(ERRORTOKEN);
        }
        if (altcol <= tok->altindstack[tok->indent]) {
          return MAKE_TOKEN(indenterror(tok));
        }
        tok->pendin++;
        tok->indstack[++tok->indent] = col;
        tok->altindstack[tok->indent] = altcol;
      } else /* col < tok->indstack[tok->indent] */ {
        /* Dedent -- any number, must be consistent */
        while (tok->indent > 0 && col < tok->indstack[tok->indent]) {
          tok->pendin--;
          tok->indent--;
        }
        if (col != tok->indstack[tok->indent]) {
          tok->done = E_DEDENT;
          tok->cur = tok->inp;
          return MAKE_TOKEN(ERRORTOKEN);
        }
        if (altcol != tok->altindstack[tok->indent]) {
          return MAKE_TOKEN(indenterror(tok));
        }
      }
    }
  }

  tok->start = tok->cur;
  tok->starting_col_offset = tok->col_offset;

  /* Return pending indents/dedents */
  if (tok->pendin != 0) {
    if (tok->pendin < 0) {
      if (tok->tok_extra_tokens) {
        p_start = tok->cur;
        p_end = tok->cur;
      }
      tok->pendin++;
      return MAKE_TOKEN(DEDENT);
    } else {
      if (tok->tok_extra_tokens) {
        p_start = tok->buf;
        p_end = tok->cur;
      }
      tok->pendin--;
      return MAKE_TOKEN(INDENT);
    }
  }

  /* Peek ahead at the next character */
  c = tok_nextc(tok);
  tok_backup(tok, c);
  /* Check if we are closing an async function */
  if (tok->async_def &&
      !blankline
      /* Due to some implementation artifacts of type comments,
       * a TYPE_COMMENT at the start of a function won't set an
       * indentation level and it will produce a NEWLINE after it.
       * To avoid spuriously ending an async function due to this,
       * wait until we have some non-newline char in front of us. */
      && c != '\n' &&
      tok->level == 0
      /* There was a NEWLINE after ASYNC DEF,
         so we're past the signature. */
      && tok->async_def_nl
      /* Current indentation level is less than where
         the async function was defined */
      && tok->async_def_indent >= tok->indent) {
    tok->async_def = 0;
    tok->async_def_indent = 0;
    tok->async_def_nl = 0;
  }

again:
  tok->start = NULL;
  /* Skip spaces */
  do {
    c = tok_nextc(tok);
  } while (c == ' ' || c == '\t' || c == '\014');

  /* Set start of current token */
  tok->start = tok->cur == NULL ? NULL : tok->cur - 1;
  tok->starting_col_offset = tok->col_offset - 1;

  /* Skip comment, unless it's a type comment */
  if (c == '#') {

    const char *p = NULL;
    const char *prefix, *type_start;
    int current_starting_col_offset;

    while (c != EOF && c != '\n' && c != '\r') {
      c = tok_nextc(tok);
    }

    if (tok->tok_extra_tokens) {
      p = tok->start;
    }

    if (tok->type_comments) {
      p = tok->start;
      current_starting_col_offset = tok->starting_col_offset;
      prefix = type_comment_prefix;
      while (*prefix && p < tok->cur) {
        if (*prefix == ' ') {
          while (*p == ' ' || *p == '\t') {
            p++;
            current_starting_col_offset++;
          }
        } else if (*prefix == *p) {
          p++;
          current_starting_col_offset++;
        } else {
          break;
        }

        prefix++;
      }

      /* This is a type comment if we matched all of type_comment_prefix. */
      if (!*prefix) {
        int is_type_ignore = 1;
        // +6 in order to skip the word 'ignore'
        const char *ignore_end = p + 6;
        const int ignore_end_col_offset = current_starting_col_offset + 6;
        tok_backup(tok, c); /* don't eat the newline or EOF */

        type_start = p;

        /* A TYPE_IGNORE is "type: ignore" followed by the end of the token
         * or anything ASCII and non-alphanumeric. */
        is_type_ignore =
            (tok->cur >= ignore_end && memcmp(p, "ignore", 6) == 0 &&
             !(tok->cur > ignore_end && ((unsigned char)ignore_end[0] >= 128 ||
                                         Py_ISALNUM(ignore_end[0]))));

        if (is_type_ignore) {
          p_start = ignore_end;
          p_end = tok->cur;

          /* If this type ignore is the only thing on the line, consume the
           * newline also. */
          if (blankline) {
            tok_nextc(tok);
            tok->atbol = 1;
          }
          return MAKE_TYPE_COMMENT_TOKEN(TYPE_IGNORE, ignore_end_col_offset,
                                         tok->col_offset);
        } else {
          p_start = type_start;
          p_end = tok->cur;
          return MAKE_TYPE_COMMENT_TOKEN(
              TYPE_COMMENT, current_starting_col_offset, tok->col_offset);
        }
      }
    }
    if (tok->tok_extra_tokens) {
      tok_backup(tok, c); /* don't eat the newline or EOF */
      p_start = p;
      p_end = tok->cur;
      tok->comment_newline = blankline;
      return MAKE_TOKEN(COMMENT);
    }
  }

  if (tok->done == E_INTERACT_STOP) {
    return MAKE_TOKEN(ENDMARKER);
  }

  /* Check for EOF and errors now */
  if (c == EOF) {
    if (tok->level) {
      return MAKE_TOKEN(ERRORTOKEN);
    }
    return MAKE_TOKEN(tok->done == E_EOF ? ENDMARKER : ERRORTOKEN);
  }

  /* Identifier (most frequent token!) */
  nonascii = 0;
  if (is_potential_identifier_start(c)) {
    /* Process the various legal combinations of b"", r"", u"", and f"". */
    int saw_b = 0, saw_r = 0, saw_u = 0, saw_f = 0;
    while (1) {
      if (!(saw_b || saw_u || saw_f) && (c == 'b' || c == 'B'))
        saw_b = 1;
      /* Since this is a backwards compatibility support literal we don't
         want to support it in arbitrary order like byte literals. */
      else if (!(saw_b || saw_u || saw_r || saw_f) && (c == 'u' || c == 'U')) {
        saw_u = 1;
      }
      /* ur"" and ru"" are not supported */
      else if (!(saw_r || saw_u) && (c == 'r' || c == 'R')) {
        saw_r = 1;
      } else if (!(saw_f || saw_b || saw_u) && (c == 'f' || c == 'F')) {
        saw_f = 1;
      } else {
        break;
      }
      c = tok_nextc(tok);
      if (c == '"' || c == '\'') {
        if (saw_f) {
          goto f_string_quote;
        }
        goto letter_quote;
      }
    }
    while (is_potential_identifier_char(c)) {
      if (c >= 128) {
        nonascii = 1;
      }
      c = tok_nextc(tok);
    }
    tok_backup(tok, c);
    if (nonascii && !verify_identifier(tok)) {
      return MAKE_TOKEN(ERRORTOKEN);
    }

    p_start = tok->start;
    p_end = tok->cur;

    /* async/await parsing block. */
    if (tok->cur - tok->start == 5 && tok->start[0] == 'a') {
      /* May be an 'async' or 'await' token.  For Python 3.7 or
         later we recognize them unconditionally.  For Python
         3.5 or 3.6 we recognize 'async' in front of 'def', and
         either one inside of 'async def'.  (Technically we
         shouldn't recognize these at all for 3.4 or earlier,
         but there's no *valid* Python 3.4 code that would be
         rejected, and async functions will be rejected in a
         later phase.) */
      if (!tok->async_hacks || tok->async_def) {
        /* Always recognize the keywords. */
        if (memcmp(tok->start, "async", 5) == 0) {
          return MAKE_TOKEN(ASYNC);
        }
        if (memcmp(tok->start, "await", 5) == 0) {
          return MAKE_TOKEN(AWAIT);
        }
      } else if (memcmp(tok->start, "async", 5) == 0) {
        /* The current token is 'async'.
           Look ahead one token to see if that is 'def'. */

        struct tok_state ahead_tok;
        struct token ahead_token;
        _PyToken_Init(&ahead_token);
        int ahead_tok_kind;

        memcpy(&ahead_tok, tok, sizeof(ahead_tok));
        ahead_tok_kind =
            tok_get_normal_mode(&ahead_tok, current_tok, &ahead_token);

        if (ahead_tok_kind == NAME && ahead_tok.cur - ahead_tok.start == 3 &&
            memcmp(ahead_tok.start, "def", 3) == 0) {
          /* The next token is going to be 'def', so instead of
             returning a plain NAME token, return ASYNC. */
          tok->async_def_indent = tok->indent;
          tok->async_def = 1;
          _PyToken_Free(&ahead_token);
          return MAKE_TOKEN(ASYNC);
        }
        _PyToken_Free(&ahead_token);
      }
    }

    return MAKE_TOKEN(NAME);
  }

  if (c == '\r') {
    c = tok_nextc(tok);
  }

  /* Newline */
  if (c == '\n') {
    tok->atbol = 1;
    if (blankline || tok->level > 0) {
      if (tok->tok_extra_tokens) {
        if (tok->comment_newline) {
          tok->comment_newline = 0;
        }
        p_start = tok->start;
        p_end = tok->cur;
        return MAKE_TOKEN(NL);
      }
      goto nextline;
    }
    if (tok->comment_newline && tok->tok_extra_tokens) {
      tok->comment_newline = 0;
      p_start = tok->start;
      p_end = tok->cur;
      return MAKE_TOKEN(NL);
    }
    p_start = tok->start;
    p_end = tok->cur - 1; /* Leave '\n' out of the string */
    tok->cont_line = 0;
    if (tok->async_def) {
      /* We're somewhere inside an 'async def' function, and
         we've encountered a NEWLINE after its signature. */
      tok->async_def_nl = 1;
    }
    return MAKE_TOKEN(NEWLINE);
  }

  /* Period or number starting with period? */
  if (c == '.') {
    c = tok_nextc(tok);
    if (isdigit(c)) {
      goto fraction;
    } else if (c == '.') {
      c = tok_nextc(tok);
      if (c == '.') {
        p_start = tok->start;
        p_end = tok->cur;
        return MAKE_TOKEN(ELLIPSIS);
      } else {
        tok_backup(tok, c);
      }
      tok_backup(tok, '.');
    } else {
      tok_backup(tok, c);
    }
    p_start = tok->start;
    p_end = tok->cur;
    return MAKE_TOKEN(DOT);
  }

  /* Number */
  if (isdigit(c)) {
    if (c == '0') {
      /* Hex, octal or binary -- maybe. */
      c = tok_nextc(tok);
      if (c == 'x' || c == 'X') {
        /* Hex */
        c = tok_nextc(tok);
        do {
          if (c == '_') {
            c = tok_nextc(tok);
          }
          if (!isxdigit(c)) {
            tok_backup(tok, c);
            return MAKE_TOKEN(syntaxerror(tok, "invalid hexadecimal literal"));
          }
          do {
            c = tok_nextc(tok);
          } while (isxdigit(c));
        } while (c == '_');
        if (!verify_end_of_number(tok, c, "hexadecimal")) {
          return MAKE_TOKEN(ERRORTOKEN);
        }
      } else if (c == 'o' || c == 'O') {
        /* Octal */
        c = tok_nextc(tok);
        do {
          if (c == '_') {
            c = tok_nextc(tok);
          }
          if (c < '0' || c >= '8') {
            if (isdigit(c)) {
              return MAKE_TOKEN(
                  syntaxerror(tok, "invalid digit '%c' in octal literal", c));
            } else {
              tok_backup(tok, c);
              return MAKE_TOKEN(syntaxerror(tok, "invalid octal literal"));
            }
          }
          do {
            c = tok_nextc(tok);
          } while ('0' <= c && c < '8');
        } while (c == '_');
        if (isdigit(c)) {
          return MAKE_TOKEN(
              syntaxerror(tok, "invalid digit '%c' in octal literal", c));
        }
        if (!verify_end_of_number(tok, c, "octal")) {
          return MAKE_TOKEN(ERRORTOKEN);
        }
      } else if (c == 'b' || c == 'B') {
        /* Binary */
        c = tok_nextc(tok);
        do {
          if (c == '_') {
            c = tok_nextc(tok);
          }
          if (c != '0' && c != '1') {
            if (isdigit(c)) {
              return MAKE_TOKEN(
                  syntaxerror(tok, "invalid digit '%c' in binary literal", c));
            } else {
              tok_backup(tok, c);
              return MAKE_TOKEN(syntaxerror(tok, "invalid binary literal"));
            }
          }
          do {
            c = tok_nextc(tok);
          } while (c == '0' || c == '1');
        } while (c == '_');
        if (isdigit(c)) {
          return MAKE_TOKEN(
              syntaxerror(tok, "invalid digit '%c' in binary literal", c));
        }
        if (!verify_end_of_number(tok, c, "binary")) {
          return MAKE_TOKEN(ERRORTOKEN);
        }
      } else {
        int nonzero = 0;
        /* maybe old-style octal; c is first char of it */
        /* in any case, allow '0' as a literal */
        while (1) {
          if (c == '_') {
            c = tok_nextc(tok);
            if (!isdigit(c)) {
              tok_backup(tok, c);
              return MAKE_TOKEN(syntaxerror(tok, "invalid decimal literal"));
            }
          }
          if (c != '0') {
            break;
          }
          c = tok_nextc(tok);
        }
        char *zeros_end = tok->cur;
        if (isdigit(c)) {
          nonzero = 1;
          c = tok_decimal_tail(tok);
          if (c == 0) {
            return MAKE_TOKEN(ERRORTOKEN);
          }
        }
        if (c == '.') {
          c = tok_nextc(tok);
          goto fraction;
        } else if (c == 'e' || c == 'E') {
          goto exponent;
        } else if (c == 'j' || c == 'J') {
          goto imaginary;
        } else if (nonzero && !tok->tok_extra_tokens) {
          /* Old-style octal: now disallowed. */
          tok_backup(tok, c);
          return MAKE_TOKEN(syntaxerror_known_range(
              tok, (int)(tok->start + 1 - tok->line_start),
              (int)(zeros_end - tok->line_start),
              "leading zeros in decimal integer "
              "literals are not permitted; "
              "use an 0o prefix for octal integers"));
        }
        if (!verify_end_of_number(tok, c, "decimal")) {
          return MAKE_TOKEN(ERRORTOKEN);
        }
      }
    } else {
      /* Decimal */
      c = tok_decimal_tail(tok);
      if (c == 0) {
        return MAKE_TOKEN(ERRORTOKEN);
      }
      {
        /* Accept floating point numbers. */
        if (c == '.') {
          c = tok_nextc(tok);
        fraction:
          /* Fraction */
          if (isdigit(c)) {
            c = tok_decimal_tail(tok);
            if (c == 0) {
              return MAKE_TOKEN(ERRORTOKEN);
            }
          }
        }
        if (c == 'e' || c == 'E') {
          int e;
        exponent:
          e = c;
          /* Exponent part */
          c = tok_nextc(tok);
          if (c == '+' || c == '-') {
            c = tok_nextc(tok);
            if (!isdigit(c)) {
              tok_backup(tok, c);
              return MAKE_TOKEN(syntaxerror(tok, "invalid decimal literal"));
            }
          } else if (!isdigit(c)) {
            tok_backup(tok, c);
            if (!verify_end_of_number(tok, e, "decimal")) {
              return MAKE_TOKEN(ERRORTOKEN);
            }
            tok_backup(tok, e);
            p_start = tok->start;
            p_end = tok->cur;
            return MAKE_TOKEN(NUMBER);
          }
          c = tok_decimal_tail(tok);
          if (c == 0) {
            return MAKE_TOKEN(ERRORTOKEN);
          }
        }
        if (c == 'j' || c == 'J') {
          /* Imaginary part */
        imaginary:
          c = tok_nextc(tok);
          if (!verify_end_of_number(tok, c, "imaginary")) {
            return MAKE_TOKEN(ERRORTOKEN);
          }
        } else if (!verify_end_of_number(tok, c, "decimal")) {
          return MAKE_TOKEN(ERRORTOKEN);
        }
      }
    }
    tok_backup(tok, c);
    p_start = tok->start;
    p_end = tok->cur;
    return MAKE_TOKEN(NUMBER);
  }

f_string_quote:
  if (((tolower(*tok->start) == 'f' || tolower(*tok->start) == 'r') &&
       (c == '\'' || c == '"'))) {
    int quote = c;
    int quote_size = 1; /* 1 or 3 */

    /* Nodes of type STRING, especially multi line strings
       must be handled differently in order to get both
       the starting line number and the column offset right.
       (cf. issue 16806) */
    tok->first_lineno = tok->lineno;
    tok->multi_line_start = tok->line_start;

    /* Find the quote size and start of string */
    int after_quote = tok_nextc(tok);
    if (after_quote == quote) {
      int after_after_quote = tok_nextc(tok);
      if (after_after_quote == quote) {
        quote_size = 3;
      } else {
        // TODO: Check this
        tok_backup(tok, after_after_quote);
        tok_backup(tok, after_quote);
      }
    }
    if (after_quote != quote) {
      tok_backup(tok, after_quote);
    }

    p_start = tok->start;
    p_end = tok->cur;
    if (tok->tok_mode_stack_index + 1 >= MAXFSTRINGLEVEL) {
      return MAKE_TOKEN(syntaxerror(tok, "too many nested f-strings"));
    }
    tokenizer_mode *the_current_tok = TOK_NEXT_MODE(tok);
    the_current_tok->kind = TOK_FSTRING_MODE;
    the_current_tok->f_string_quote = quote;
    the_current_tok->f_string_quote_size = quote_size;
    the_current_tok->f_string_start = tok->start;
    the_current_tok->f_string_multi_line_start = tok->line_start;
    the_current_tok->f_string_line_start = tok->lineno;
    the_current_tok->f_string_start_offset = -1;
    the_current_tok->f_string_multi_line_start_offset = -1;
    the_current_tok->last_expr_buffer = NULL;
    the_current_tok->last_expr_size = 0;
    the_current_tok->last_expr_end = -1;
    the_current_tok->f_string_debug = 0;

    switch (*tok->start) {
    case 'F':
    case 'f':
      the_current_tok->f_string_raw = tolower(*(tok->start + 1)) == 'r';
      break;
    case 'R':
    case 'r':
      the_current_tok->f_string_raw = 1;
      break;
    default:
      Py_UNREACHABLE();
    }

    the_current_tok->curly_bracket_depth = 0;
    the_current_tok->curly_bracket_expr_start_depth = -1;
    return MAKE_TOKEN(FSTRING_START);
  }

letter_quote:
  /* String */
  if (c == '\'' || c == '"') {
    int quote = c;
    int quote_size = 1; /* 1 or 3 */
    int end_quote_size = 0;

    /* Nodes of type STRING, especially multi line strings
       must be handled differently in order to get both
       the starting line number and the column offset right.
       (cf. issue 16806) */
    tok->first_lineno = tok->lineno;
    tok->multi_line_start = tok->line_start;

    /* Find the quote size and start of string */
    c = tok_nextc(tok);
    if (c == quote) {
      c = tok_nextc(tok);
      if (c == quote) {
        quote_size = 3;
      } else {
        end_quote_size = 1; /* empty string found */
      }
    }
    if (c != quote) {
      tok_backup(tok, c);
    }

    /* Get rest of string */
    while (end_quote_size != quote_size) {
      c = tok_nextc(tok);
      if (tok->done == E_ERROR) {
        return MAKE_TOKEN(ERRORTOKEN);
      }
      if (tok->done == E_DECODE) {
        break;
      }
      if (c == EOF || (quote_size == 1 && c == '\n')) {
        assert(tok->multi_line_start != NULL);
        // shift the tok_state's location into
        // the start of string, and report the error
        // from the initial quote character
        tok->cur = (char *)tok->start;
        tok->cur++;
        tok->line_start = tok->multi_line_start;
        int start = tok->lineno;
        tok->lineno = tok->first_lineno;

        if (INSIDE_FSTRING(tok)) {
          /* When we are in an f-string, before raising the
           * unterminated string literal error, check whether
           * does the initial quote matches with f-strings quotes
           * and if it is, then this must be a missing '}' token
           * so raise the proper error */
          tokenizer_mode *the_current_tok = TOK_GET_MODE(tok);
          if (the_current_tok->f_string_quote == quote &&
              the_current_tok->f_string_quote_size == quote_size) {
            return MAKE_TOKEN(
                syntaxerror(tok, "f-string: expecting '}'", start));
          }
        }

        if (quote_size == 3) {
          syntaxerror(tok,
                      "unterminated triple-quoted string literal"
                      " (detected at line %d)",
                      start);
          if (c != '\n') {
            tok->done = E_EOFS;
          }
          return MAKE_TOKEN(ERRORTOKEN);
        } else {
          syntaxerror(tok,
                      "unterminated string literal (detected at"
                      " line %d)",
                      start);
          if (c != '\n') {
            tok->done = E_EOLS;
          }
          return MAKE_TOKEN(ERRORTOKEN);
        }
      }
      if (c == quote) {
        end_quote_size += 1;
      } else {
        end_quote_size = 0;
        if (c == '\\') {
          c = tok_nextc(tok); /* skip escaped char */
          if (c == '\r') {
            c = tok_nextc(tok);
          }
        }
      }
    }

    p_start = tok->start;
    p_end = tok->cur;
    return MAKE_TOKEN(STRING);
  }

  /* Line continuation */
  if (c == '\\') {
    if ((c = tok_continuation_line(tok)) == -1) {
      return MAKE_TOKEN(ERRORTOKEN);
    }
    tok->cont_line = 1;
    goto again; /* Read next line */
  }

  /* Punctuation character */
  int is_punctuation = (c == ':' || c == '}' || c == '!' || c == '{');
  if (is_punctuation && INSIDE_FSTRING(tok) &&
      INSIDE_FSTRING_EXPR(current_tok)) {
    /* This code block gets executed before the curly_bracket_depth is
     * incremented by the `{` case, so for ensuring that we are on the 0th
     * level, we need to adjust it manually */
    int cursor = current_tok->curly_bracket_depth - (c != '{');
    int in_format_spec = current_tok->in_format_spec;
    int cursor_in_format_with_debug =
        cursor == 1 && (current_tok->f_string_debug || in_format_spec);
    int cursor_valid = cursor == 0 || cursor_in_format_with_debug;
    if (cursor_valid && !update_fstring_expr(tok, c)) {
      return MAKE_TOKEN(ENDMARKER);
    }
    if (cursor_valid && c != '{' && set_fstring_expr(tok, token, c)) {
      return MAKE_TOKEN(ERRORTOKEN);
    }

    if (c == ':' && cursor == current_tok->curly_bracket_expr_start_depth) {
      current_tok->kind = TOK_FSTRING_MODE;
      current_tok->in_format_spec = 1;
      p_start = tok->start;
      p_end = tok->cur;
      return MAKE_TOKEN(_PyToken_OneChar(c));
    }
  }

  /* Check for two-character token */
  {
    int c2 = tok_nextc(tok);
    int current_token = _PyToken_TwoChars(c, c2);
    if (current_token != OP) {
      int c3 = tok_nextc(tok);
      int current_token3 = _PyToken_ThreeChars(c, c2, c3);
      if (current_token3 != OP) {
        current_token = current_token3;
      } else {
        tok_backup(tok, c3);
      }
      p_start = tok->start;
      p_end = tok->cur;
      return MAKE_TOKEN(current_token);
    }
    tok_backup(tok, c2);
  }

  /* Keep track of parentheses nesting level */
  switch (c) {
  case '(':
  case '[':
  case '{':
    if (tok->level >= MAXLEVEL) {
      return MAKE_TOKEN(syntaxerror(tok, "too many nested parentheses"));
    }
    tok->parenstack[tok->level] = c;
    tok->parenlinenostack[tok->level] = tok->lineno;
    tok->parencolstack[tok->level] = (int)(tok->start - tok->line_start);
    tok->level++;
    if (INSIDE_FSTRING(tok)) {
      current_tok->curly_bracket_depth++;
    }
    break;
  case ')':
  case ']':
  case '}':
    if (INSIDE_FSTRING(tok) && !current_tok->curly_bracket_depth && c == '}') {
      return MAKE_TOKEN(
          syntaxerror(tok, "f-string: single '}' is not allowed"));
    }
    if (!tok->tok_extra_tokens && !tok->level) {
      return MAKE_TOKEN(syntaxerror(tok, "unmatched '%c'", c));
    }
    if (tok->level > 0) {
      tok->level--;
      int opening = tok->parenstack[tok->level];
      if (!tok->tok_extra_tokens &&
          !((opening == '(' && c == ')') || (opening == '[' && c == ']') ||
            (opening == '{' && c == '}'))) {
        /* If the opening bracket belongs to an f-string's expression
        part (e.g. f"{)}") and the closing bracket is an arbitrary
        nested expression, then instead of matching a different
        syntactical construct with it; we'll throw an unmatched
        parentheses error. */
        if (INSIDE_FSTRING(tok) && opening == '{') {
          assert(current_tok->curly_bracket_depth >= 0);
          int previous_bracket = current_tok->curly_bracket_depth - 1;
          if (previous_bracket == current_tok->curly_bracket_expr_start_depth) {
            return MAKE_TOKEN(syntaxerror(tok, "f-string: unmatched '%c'", c));
          }
        }
        if (tok->parenlinenostack[tok->level] != tok->lineno) {
          return MAKE_TOKEN(
              syntaxerror(tok,
                          "closing parenthesis '%c' does not match "
                          "opening parenthesis '%c' on line %d",
                          c, opening, tok->parenlinenostack[tok->level]));
        } else {
          return MAKE_TOKEN(
              syntaxerror(tok,
                          "closing parenthesis '%c' does not match "
                          "opening parenthesis '%c'",
                          c, opening));
        }
      }
    }

    if (INSIDE_FSTRING(tok)) {
      current_tok->curly_bracket_depth--;
      if (current_tok->curly_bracket_depth < 0) {
        return MAKE_TOKEN(syntaxerror(tok, "f-string: unmatched '%c'", c));
      }
      if (c == '}' && current_tok->curly_bracket_depth ==
                          current_tok->curly_bracket_expr_start_depth) {
        current_tok->curly_bracket_expr_start_depth--;
        current_tok->kind = TOK_FSTRING_MODE;
        current_tok->in_format_spec = 0;
        current_tok->f_string_debug = 0;
      }
    }
    break;
  default:
    break;
  }

  if (!Py_UNICODE_ISPRINTABLE(c)) {
    return MAKE_TOKEN(
        syntaxerror(tok, "invalid non-printable character U+%04X", c));
  }

  if (c == '=' && INSIDE_FSTRING_EXPR(current_tok)) {
    current_tok->f_string_debug = 1;
  }

  /* Punctuation character */
  p_start = tok->start;
  p_end = tok->cur;
  return MAKE_TOKEN(_PyToken_OneChar(c));
}

static int tok_get_fstring_mode(struct tok_state *tok,
                                tokenizer_mode *current_tok,
                                struct token *token) {
  const char *p_start = NULL;
  const char *p_end = NULL;
  int end_quote_size = 0;
  int unicode_escape = 0;

  tok->start = tok->cur;
  tok->first_lineno = tok->lineno;
  tok->starting_col_offset = tok->col_offset;

  // If we start with a bracket, we defer to the normal mode as there is nothing
  // for us to tokenize before it.
  int start_char = tok_nextc(tok);
  if (start_char == '{') {
    int peek1 = tok_nextc(tok);
    tok_backup(tok, peek1);
    tok_backup(tok, start_char);
    if (peek1 != '{') {
      current_tok->curly_bracket_expr_start_depth++;
      if (current_tok->curly_bracket_expr_start_depth >= MAX_EXPR_NESTING) {
        return MAKE_TOKEN(
            syntaxerror(tok, "f-string: expressions nested too deeply"));
      }
      TOK_GET_MODE(tok)->kind = TOK_REGULAR_MODE;
      return tok_get_normal_mode(tok, current_tok, token);
    }
  } else {
    tok_backup(tok, start_char);
  }

  // Check if we are at the end of the string
  for (int i = 0; i < current_tok->f_string_quote_size; i++) {
    int quote = tok_nextc(tok);
    if (quote != current_tok->f_string_quote) {
      tok_backup(tok, quote);
      goto f_string_middle;
    }
  }

  if (current_tok->last_expr_buffer != NULL) {
    PyMem_Free(current_tok->last_expr_buffer);
    current_tok->last_expr_buffer = NULL;
    current_tok->last_expr_size = 0;
    current_tok->last_expr_end = -1;
  }

  p_start = tok->start;
  p_end = tok->cur;
  tok->tok_mode_stack_index--;
  return MAKE_TOKEN(FSTRING_END);

f_string_middle:

  // TODO: This is a bit of a hack, but it works for now. We need to find a
  // better way to handle this.
  tok->multi_line_start = tok->line_start;
  while (end_quote_size != current_tok->f_string_quote_size) {
    int c = tok_nextc(tok);
    if (tok->done == E_ERROR || tok->done == E_DECODE) {
      return MAKE_TOKEN(ERRORTOKEN);
    }
    int in_format_spec =
        (current_tok->in_format_spec && INSIDE_FSTRING_EXPR(current_tok));

    if (c == EOF || (current_tok->f_string_quote_size == 1 && c == '\n')) {
      if (tok->decoding_erred) {
        return MAKE_TOKEN(ERRORTOKEN);
      }

      // If we are in a format spec and we found a newline,
      // it means that the format spec ends here and we should
      // return to the regular mode.
      if (in_format_spec && c == '\n') {
        tok_backup(tok, c);
        TOK_GET_MODE(tok)->kind = TOK_REGULAR_MODE;
        current_tok->in_format_spec = 0;
        p_start = tok->start;
        p_end = tok->cur;
        return MAKE_TOKEN(FSTRING_MIDDLE);
      }

      assert(tok->multi_line_start != NULL);
      // shift the tok_state's location into
      // the start of string, and report the error
      // from the initial quote character
      tok->cur = (char *)current_tok->f_string_start;
      tok->cur++;
      tok->line_start = current_tok->f_string_multi_line_start;
      int start = tok->lineno;

      tokenizer_mode *the_current_tok = TOK_GET_MODE(tok);
      tok->lineno = the_current_tok->f_string_line_start;

      if (current_tok->f_string_quote_size == 3) {
        syntaxerror(tok,
                    "unterminated triple-quoted f-string literal"
                    " (detected at line %d)",
                    start);
        if (c != '\n') {
          tok->done = E_EOFS;
        }
        return MAKE_TOKEN(ERRORTOKEN);
      } else {
        return MAKE_TOKEN(
            syntaxerror(tok,
                        "unterminated f-string literal (detected at"
                        " line %d)",
                        start));
      }
    }

    if (c == current_tok->f_string_quote) {
      end_quote_size += 1;
      continue;
    } else {
      end_quote_size = 0;
    }

    if (c == '{') {
      if (!update_fstring_expr(tok, c)) {
        return MAKE_TOKEN(ENDMARKER);
      }
      int peek = tok_nextc(tok);
      if (peek != '{' || in_format_spec) {
        tok_backup(tok, peek);
        tok_backup(tok, c);
        current_tok->curly_bracket_expr_start_depth++;
        if (current_tok->curly_bracket_expr_start_depth >= MAX_EXPR_NESTING) {
          return MAKE_TOKEN(
              syntaxerror(tok, "f-string: expressions nested too deeply"));
        }
        TOK_GET_MODE(tok)->kind = TOK_REGULAR_MODE;
        current_tok->in_format_spec = 0;
        p_start = tok->start;
        p_end = tok->cur;
      } else {
        p_start = tok->start;
        p_end = tok->cur - 1;
      }
      return MAKE_TOKEN(FSTRING_MIDDLE);
    } else if (c == '}') {
      if (unicode_escape) {
        p_start = tok->start;
        p_end = tok->cur;
        return MAKE_TOKEN(FSTRING_MIDDLE);
      }
      int peek = tok_nextc(tok);

      // The tokenizer can only be in the format spec if we have already
      // completed the expression scanning (indicated by the end of the
      // expression being set) and we are not at the top level of the bracket
      // stack (-1 is the top level). Since format specifiers can't legally use
      // double brackets, we can bypass it here.
      int cursor = current_tok->curly_bracket_depth;
      if (peek == '}' && !in_format_spec && cursor == 0) {
        p_start = tok->start;
        p_end = tok->cur - 1;
      } else {
        tok_backup(tok, peek);
        tok_backup(tok, c);
        TOK_GET_MODE(tok)->kind = TOK_REGULAR_MODE;
        p_start = tok->start;
        p_end = tok->cur;
      }
      return MAKE_TOKEN(FSTRING_MIDDLE);
    } else if (c == '\\') {
      int peek = tok_nextc(tok);
      if (peek == '\r') {
        peek = tok_nextc(tok);
      }
      // Special case when the backslash is right before a curly
      // brace. We have to restore and return the control back
      // to the loop for the next iteration.
      if (peek == '{' || peek == '}') {
        if (!current_tok->f_string_raw) {
          if (warn_invalid_escape_sequence0(tok, peek)) {
            return MAKE_TOKEN(ERRORTOKEN);
          }
        }
        tok_backup(tok, peek);
        continue;
      }

      if (!current_tok->f_string_raw) {
        if (peek == 'N') {
          /* Handle named unicode escapes (\N{BULLET}) */
          peek = tok_nextc(tok);
          if (peek == '{') {
            unicode_escape = 1;
          } else {
            tok_backup(tok, peek);
          }
        }
      } /* else {
          skip the escaped character
      }*/
    }
  }

  // Backup the f-string quotes to emit a final FSTRING_MIDDLE and
  // add the quotes to the FSTRING_END in the next tokenizer iteration.
  for (int i = 0; i < current_tok->f_string_quote_size; i++) {
    tok_backup(tok, current_tok->f_string_quote);
  }
  p_start = tok->start;
  p_end = tok->cur;
  return MAKE_TOKEN(FSTRING_MIDDLE);
}

static int tok_get(struct tok_state *tok, struct token *token) {
  tokenizer_mode *current_tok = TOK_GET_MODE(tok);
  if (current_tok->kind == TOK_REGULAR_MODE) {
    return tok_get_normal_mode(tok, current_tok, token);
  } else {
    return tok_get_fstring_mode(tok, current_tok, token);
  }
}

static int _PyTokenizer_Get(struct tok_state *tok, struct token *token) {
  int result = tok_get(tok, token);
  if (tok->decoding_erred) {
    result = ERRORTOKEN;
    tok->done = E_DECODE;
  }
  return result;
}
