# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau

import types
import inspect
import ast
import json
import numpy as np

from textwrap import dedent
from itertools import chain
from collections import deque
from nkl.lean import py_to_lean

# This is a custom JSON encoder for use with AST nodes.
# The AST nodes are not handled by the default encoder.
# For an AST node, we return a dictionary with the class
# name mapped to the object dictionary. If the object
# dictionary is empty we just return the class name.
# e.g.
# Binop(left=l,op=o,right=r), becomes:
#    { BinOp : { left:l, op:o, right:r } }
# Pass(), becomes
#    'Pass'
#
# For anything else not handled by the default
# encoder, we return "...", the Ellipsis.
# Conveniently, Ellipsis is one of the things
# that isn't handled, so it is properly mapped.

# See also: NKL/Python.lean for the Lean side

class Enc(json.JSONEncoder):
  def default(self, obj):
    if isinstance(obj, ast.AST):
      if len(obj.__dict__) == 0:
        return obj.__class__.__name__
      else:
        return { obj.__class__.__name__:obj.__dict__ }
    try:
      return super().default(obj)
    except Exception:
      return "..."

# Referenced names, that are not functions are placed in the
# global environment. Unlike functions, these values cannot
# reflected on using the ast module (the inspect module can only
# fetch sources for a limited number of types). This function
# provides an encoding for the global environment for a common
# set of types.

class Unsupported(Exception): pass

def encode_for_env(val):
  match val:
    case bool(b): return {'bool':b}
    case int(i): return {'int':i}
    case float(f): return {'float':f}
    case str(s): return {'str':s}
    case types.NoneType(): return None
    case tuple(t): return {'tuple': list(map(encode_for_env, t))}
    case list(l): return {'list': list(map(encode_for_env, l))}
    case types.ModuleType(): return {'mod':val.__name__}
    case np.ndarray():
      return {
          'tensor': {
            'dtype': encode_for_env(str(val.dtype)),
            'shape': encode_for_env(val.shape)
            }
          }
    case _:
      raise Unsupported(f"global value type: {val.__class__.__name__}")

class Parser(ast.NodeVisitor):
  def __init__(self, f: types.FunctionType):
    super().__init__()
    self.workq = deque()
    self.funcs = {}
    self.globals = {}
    self.args = []
    self.kwargs = {}
    self.entry = f.__module__ + "." + f.__name__
    self.ref_global(self.entry, f)
    self.do_work()

  def json(self):
    d = { 'entry': self.entry
        , 'funcs': self.funcs
        , 'args' : self.args
        , 'kwargs' : self.kwargs
        , 'globals': self.globals
        }
    return json.dumps(d, cls=Enc)

  # TODO: just a placeholder for testing
  def load(self):
    py_to_lean(self.json())

  def apply_args(self, *args, **kwargs):
    self.args = []
    self.kwargs = {}
    d = {}
    for arg in args:
      self.reference(d, '_', arg)
      try: self.args.append(d.popitem()[1])
      except Exception:
        raise Exception("Unsupported argument type")
    for k,v in kwargs.items():
      self.ref_arg(k, v)

  def __call__(self, *args, **kwargs):
    self.apply_args(*args, **kwargs)
    py_to_lean(self.json())

  def ref_arg(self, refname, val):
    return self.reference(self.kwargs, refname, val)

  def ref_global(self, refname, val):
    return self.reference(self.globals, refname, val)

  # resolve a reference: either populating the environment,
  # or adding new items to the work queue
  def reference(self, env, refname, val):
    f = None
    if isinstance(val, types.FunctionType):
      f = val
      fname = f.__module__ + "." + f.__name__
      val = {'fun': fname}
    else:
      try: val = encode_for_env(val)
      except Exception:
        return

    if refname in env:
      if val != env[refname]:
        assert 0, "global mismatch"
    else:
      env[refname] = val

    if f is None:
      return
    try:
      match ast.parse(dedent(inspect.getsource(f))):
        case ast.Module([ast.FunctionDef(_, args, body)]):
          self.workq.append((fname, f, args, body))
        case _:
          assert 0, "expecting function definition"
    except Exception:
      pass

  def do_work(self):
    while len(self.workq) > 0:
      fullname, f, args, body = self.workq.popleft()
      if fullname in self.funcs:
        continue
      self.funcs[fullname] = self.translate(f, args, body)

  def translate(self, f: types.FunctionType, args: ast.arguments, body: [ast.AST]):
    self.f = f
    for s in body:
      self.visit(s)
    return { 'source': inspect.getsource(f)
           , 'args': args
           , 'defaults': list(self.fun_defaults(f))
           , 'body': body
           }

  # A best-effort dependency finder.
  # This is a valid approach because we only need to find
  # the expressions that refer to external names, it is ok
  # if we find other uses of potentially global names
  # and fail to understand them; as long as we find and record
  # the "real" uses into the environment for the Lean code.
  def lookup(self, s):
    return self.f.__globals__.get(s) or self.f.__builtins__.get(s)

  def visit_Name(self, node):
    if node.id not in self.f.__code__.co_names:
      return
    try:
      y = self.lookup(node.id)
      self.ref_global(node.id, y)
      return node.id, y
    except Unsupported as e:
      raise e
    except Exception:
      return

  def visit_Attribute(self, node):
    if node.ctx == ast.Store() or \
       node.attr not in self.f.__code__.co_names:
         return
    try:
      n, x = self.visit(node.value)
      n = n + "." + node.attr
      y = getattr(x, node.attr)
      self.ref_global(n, y)
      return n, y
    except Unsupported as e:
      raise e
    except Exception:
      return

  def fun_defaults(self, f: types.FunctionType):
    if f.__defaults__ is None:
      return dict()
    names = f.__code__.co_varnames[:f.__code__.co_argcount]
    tbl = { n:v for (n,v) in zip(reversed(names), reversed(f.__defaults__)) }
    if f.__kwdefaults__ is not None:
      tbl.update(f.__kwdefaults__)
    def is_ok(x):
      if x is None or isinstance(x, (int, float, str)):
        return True
      if isinstance(x, types.FunctionType):
        # TODO: this could be incorrect if default
        # is using an alternate name for the function
        self.ref_global(x.__name__, x)
      return False
    return { n:v for (n,v) in tbl.items() if is_ok(v) }
