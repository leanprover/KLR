/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Serde.Attr
import KLR.Serde.Elab
import KLR.Util
import Lean

/-!
# Abstract syntax of Python functions

Mostly 1-to-1 translation of the Python AST to lean.
see: https://docs.python.org/3/library/ast.html
-/

namespace KLR.Python
open Lean (FromJson ToJson)
open Serde (FromCBOR ToCBOR)
open Util (FromSexp ToSexp)

export Core (Pos)

@[serde tag = 1]
inductive Const where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | ellipsis
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
This context comes from the Python AST. The different hints
indicated how an l-value term is being used. For example:

  x = 1         # x is store context
  return x + 5  # x is load context
  del x         # x is del context

The store hint is used by the tracing implementation for
simplicity: we do not try to resolve names that are being
"stored" to.
-/

@[serde tag = 2]
enum Ctx where
  | load | store | del
  deriving FromCBOR, ToCBOR

-- Python boolean (logical) operators
@[serde tag = 3]
enum BoolOp where
  | land | lor
  deriving FromCBOR, ToCBOR

-- Python comparison operators
@[serde tag = 4]
enum CmpOp where
  | eq | ne | lt | le | gt | ge | is | isNot | isIn | notIn
  deriving FromCBOR, ToCBOR

-- Python unary operators
@[serde tag = 5]
enum UnaryOp where
  | invert | not | uadd | usub
  deriving FromCBOR, ToCBOR

-- Python binary operators
@[serde tag = 6]
enum BinOp where
  | add | sub | mul | matmul | div | mod | pow
  | lshift | rshift | or | xor | and
  | floor -- the '//' operator in Python
  deriving FromCBOR, ToCBOR

mutual
@[serde tag = 7]
structure Expr where
  expr : Expr'
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 8]
inductive Expr' where
  | const (value : Const)
    -- TODO we don't need tensor here, it can be NKI only
  | tensor (shape : List Expr) (dtype : String)
  | name (id : String) (ctx : Ctx)
  | attr (value : Expr) (id : String) (ctx : Ctx)
  | tuple (xs: List Expr) (ctx : Ctx)
  | list (xs: List Expr) (ctx : Ctx)
  | subscript (tensor: Expr) (index: Expr) (ctx : Ctx)
  | slice (l u step: Option Expr)
  | boolOp (op : BoolOp) (values : List Expr)
  | binOp (op : BinOp) (left right : Expr)
  | unaryOp (op : UnaryOp) (operand : Expr)
  | compare (left : Expr) (ops : List CmpOp) (comparators : List Expr)
  | ifExp (test body orelse : Expr)
  | call (f: Expr) (args: List Expr) (keywords : List Keyword)
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 9]
structure Keyword where
  id : String
  value : Expr
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
end

mutual
@[serde tag = 10]
structure Stmt where
  stmt : Stmt'
  pos : Pos
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

@[serde tag = 11]
inductive Stmt' where
  | pass
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e : Expr)
  | assign (xs : List Expr) (e: Expr)
  | augAssign (x : Expr) (op : BinOp) (e : Expr)
  | annAssign (x : Expr) (annotation : Expr) (value : Option Expr)
  | ifStm (e : Expr) (thn els: List Stmt)
  | forLoop (x : Expr) (iter: Expr) (body: List Stmt) (orelse : List Stmt)
  | breakLoop
  | continueLoop
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp
end

/-
This structure is a mirror of the python arguments AST node.
If we have the following Python function:

  def f(a, b=1, /, c=2, *args, d, e=3, **kwargs): pass

then the structure will be populated with:

  posonlyargs = [a, b]
  args = [c]
  defaults = [1, 2]
  vararg = "args"
  kwonlyargs = [d, e]
  kw_defaults = [("e", 3)]
  kwarg = "kwargs"

Note, this is slightly different from the official Python AST, which
encodes the kw_defaults as a list with None for missing defaults.
-/
@[serde tag = 12]
structure Args where
  posonlyargs : List String
  args : List String
  defaults: List Expr
  vararg : Option String
  kwonlyargs : List String
  kw_defaults: List Keyword
  kwarg : Option String
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

def Args.names (args : Args) : List String :=
  args.posonlyargs ++ args.args ++ args.kwonlyargs

-- TODO: does not compute required keyword args
def Args.required (args : Args) : List String :=
  let pargs := args.posonlyargs ++ args.args
  pargs.take (pargs.length - args.defaults.length)

def Args.all_defaults (args : Args) : List Keyword :=
  let pargs := args.posonlyargs ++ args.args
  let dflt  := pargs.reverse.zip args.defaults.reverse
  let dflt  := dflt.map fun (n, e) => .mk n e { line := 0 }
  dflt ++ args.kw_defaults

@[serde tag = 13]
structure Fun where
  name : String
  line : Nat
  source : String
  args : Args
  body: List Stmt
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
A kernel is collection of:
  - the name of the main kernel function: `entry`
  - functions, including the primary function and any functions
    called by the primary func that we are able to parse
  - arguments to the primary function, the positional arguments
    are in the field `args` and the keyword argument are in the
    field `kwargs`
  - global variables referenced by any of the functions

An example of a global is:

  use_fancy_thing = true   # this will end up in globals
  def kernel():
    if use_fancy_thing:
      ...
    else:
      ...
-/
@[serde tag = 14]
structure Kernel where
  entry : String
  funcs : List Fun
  args : List Expr
  kwargs : List Keyword
  globals : List Keyword
  undefinedSymbols : List String
  deriving BEq, FromCBOR, FromJson, FromSexp, Repr, ToCBOR, ToJson, ToSexp

/-
POC: try to guess suitable arguments if none suplied (see bin/gather).
We could do a much better job, but for now just assume any missing
arguments (that do not have default values) are tensors, and provide
a small test tensor (10x10 float32).

How to do better:
  - Check type annotations from user
  - Run type inference
  - Provide command-line arguments to adjust how we pick defaults
-/
def Kernel.inferArguments (k : Kernel) : Kernel × List String :=
  if k.args.length > 0 then (k, []) else
    match inferArgs with
    | none => (k, [])
    | some [] => ({ k with args := [] }, [])
    | some args => ({ k with args := args }, [s!"Warning: inferred arbitrary values for {k.entry}"])
where
  inferArgs : Option (List Expr) := do
    let f <- k.funcs.find? fun f => f.name == k.entry
    let args := f.args.required
    let ten := { expr := .const (.int 10), pos := { line := 0 } }
    let dtype := "nki.language.float32"
    let tensors := args.map fun _ => { expr := .tensor [ten,ten] dtype, pos := { line := 0 } }
    return tensors
