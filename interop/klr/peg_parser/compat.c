/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// These functions were introduced in Python 3.10 and are used by the parser.
#if PY_MINOR_VERSION < 10
static inline PyObject *_Py_NewRef(PyObject *obj) {
  Py_INCREF(obj);
  return obj;
}
#define Py_NewRef(obj) _Py_NewRef(_PyObject_CAST(obj))

static PyObject *_PyImport_GetModuleAttrString(const char *modname,
                                               const char *attrname) {
  PyObject *mod = PyImport_ImportModule(modname);
  if (mod == NULL)
    return NULL;

  PyObject *result = PyObject_GetAttrString(mod, attrname);
  Py_DECREF(mod);
  return result;
}
#endif

// An alternate implementation of PyArena which uses our region allocator.

typedef struct _arena {
  struct region *region;
  PyObject *objects;
} PyArena;

static void _PyArena_Free(PyArena *arena) {
  if (arena) {
    if (arena->region)
      region_destroy(arena->region);
    if (arena->objects)
      Py_DECREF(arena->objects);
    PyMem_Free(arena);
  }
}

static PyArena *_PyArena_New(void) {
  PyArena *arena = (PyArena *)PyMem_Malloc(sizeof(PyArena));
  if (!arena)
    return (PyArena *)PyErr_NoMemory();

  arena->region = region_create();
  arena->objects = PyList_New(0);
  if (!arena->region || !arena->objects) {
    _PyArena_Free(arena);
    return (PyArena *)PyErr_NoMemory();
  }
  return arena;
}

static void *_PyArena_Malloc(PyArena *arena, size_t size) {
  void *p = region_alloc(arena->region, size);
  if (!p)
    return PyErr_NoMemory();
  return p;
}

static int _PyArena_AddPyObject(PyArena *arena, PyObject *obj) {
  int r = PyList_Append(arena->objects, obj);
  if (r >= 0)
    Py_DECREF(obj);
  return r;
}
