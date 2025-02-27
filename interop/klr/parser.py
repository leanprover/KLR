# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import ast
import inspect
import json
import numpy as np
import types

from collections import deque
from textwrap import dedent
from typing import List

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

# See also: KLR/Python.lean for the Lean side

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
# global environment. Unlike functions, these values cannot be
# reflected on using the ast module (the inspect module can only
# fetch sources for a limited number of types). This function
# provides an encoding for the global environment for a common
# set of types.

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
      raise Exception(f"global value type: {val.__class__.__name__}")

class Parser(ast.NodeVisitor):
  def __init__(self, f: types.FunctionType):
    super().__init__()
    self.workq = deque()
    self.funcs = {}
    self.globals = {}
    self.args = []
    self.kwargs = {}
    self.entry = f.__module__ + "." + f.__name__
    self.undefined_symbols = [] # Lean can send these back to the caller as linter errors
    self.ref_global(self.entry, f)
    self.do_work()

  def json(self):
    d = { 'entry': self.entry
        , 'funcs': self.funcs
        , 'args' : self.args
        , 'kwargs' : self.kwargs
        , 'globals': self.globals
        , 'undefined_symbols': self.undefined_symbols
        }
    return json.dumps(d, cls=Enc)

  def process_args(self, args, kwargs):
    l = []
    d = {}
    if args:
      for arg in args:
        self.reference(d, '_', arg)
        try: l.append(d.popitem()[1])
        except Exception:
          raise Exception(f"Unsupported argument type: {arg.__class__.__name__}") from None
    if kwargs:
      for k,v in kwargs.items():
        self.reference(d, k, v)
    return l, d

  def apply_args(self, *args, **kwargs):
    l, d = self.process_args(args, kwargs)
    self.args = l
    self.kwargs = d

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
      # get the source lines and starting offset in file
      src, line = inspect.getsourcelines(f)
      # remove leading indentation to prevent parse failures
      # for nested or class functions
      src = dedent("".join(src))
      match ast.parse(src):
        case ast.Module([ast.FunctionDef(_, args, body)]):
          self.workq.append((fname, src, line, f, args, body))
        case _:
          assert 0, "expecting function definition"
    except Exception:
      pass

  def do_work(self):
    while len(self.workq) > 0:
      fullname, src, line, f, args, body = self.workq.popleft()
      if fullname in self.funcs:
        continue
      self.funcs[fullname] = self.translate(src, line, f, args, body)

  def translate(self, src: str, line: int, f: types.FunctionType, args: ast.arguments, body: List[ast.AST]):
    self.f = f
    for s in body:
      self.visit(s)
    l, d = self.process_args(f.__defaults__, f.__kwdefaults__)
    args.defaults = l
    args.kw_defaults = d
    return { 'source': src
           , 'line': line
           , 'args': args
           , 'body': body
           }

  # A best-effort dependency finder.
  # This is a valid approach because we only need to find
  # the expressions that refer to external names, it is ok
  # if we find other uses of potentially global names
  # and fail to understand them; as long as we find and record
  # the "real" uses into the environment for the Lean code.
  def lookup(self, node):
    s = node.id
    if s in self.f.__globals__:
      return self.f.__globals__[s]
    if s in self.f.__builtins__:
      return self.f.__builtins__[s]
    self.undefined_symbols.append(s)
    return None

  def visit_Name(self, node):
    if node.id not in self.f.__code__.co_names:
      return
    try:
      y = self.lookup(node)
      self.ref_global(node.id, y)
      return node.id, y
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
    except AttributeError as e:
      if isinstance(e.obj, types.ModuleType):
        name = e.obj.__name__ + "." + e.name
        self.undefined_symbols.append(name)
    except Exception:
      return
