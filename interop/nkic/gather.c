/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include "frontend.h"
#include "ast_python.h"
#include "ast_python_core.h"
// TODO: only for testing
#include "ast_nki.h"

// Note: modern Pythons have PyImport_GetModuleByDef, but we need to be
// compatible with 3.9

static PyObject* get_util(const char *name) {
  PyObject *m = NULL, *attr = NULL, *f = NULL;
  PyObject *fe = PyUnicode_FromString("frontend");
  if (fe) {
    m = PyImport_GetModule(fe);
    if (m) {
      attr = PyUnicode_FromString(name);
      if (attr)
        f = PyObject_GetAttr(m, attr);
    }
  }
  Py_XDECREF(fe);
  Py_XDECREF(m);
  Py_XDECREF(attr);
  return f;
}

static struct _mod* parse_function(PyObject *f) {
  struct _mod *m = NULL; // needed for done label

  PyObject *getsrc = get_util("_get_src");
  if (!getsrc)
    return NULL;

  PyObject *args = PyTuple_New(1);
  if (!args) {
    Py_DECREF(getsrc);
    return NULL;
  }

  Py_INCREF(f);
  PyTuple_SET_ITEM(args, 0, f);
  PyObject *source = PyObject_CallObject(getsrc, args);
  Py_DECREF(args);
  Py_DECREF(getsrc);

  if (!source || !PyTuple_Check(source) || PyTuple_Size(source) != 3)
    goto done;

  PyObject *file = PyTuple_GetItem(source, 0);
  PyObject *line = PyTuple_GetItem(source, 1);
  PyObject *src  = PyTuple_GetItem(source, 2);

  if (!file || !PyUnicode_Check(file) ||
      !line || !PyLong_Check(line) ||
      !src  || !PyUnicode_Check(src))
    goto done;

  long lineno = PyLong_AsLong(line);

  Py_ssize_t size = 0;
  const char *s = PyUnicode_AsUTF8AndSize(src, &size);
  if (!s || size <= 0)
    goto done;

  printf("got source line:%ld, size:%ld, \n'%s'\n", lineno, size, s);
  m = parse_string(s, file);

done:
  Py_XDECREF(source);
  return m;
}

// TODO: This is not the full gather step, just a single parse
bool gather(struct kernel *k) {
  struct _mod *m = parse_function(k->f);
  printf("got Python AST = %p\n", m);

  bool result = m != NULL;
  free_python_ast(m);

  return result;
}
