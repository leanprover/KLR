/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Util

/-!
# Abstract syntax of Python functions

Mostly 1-to-1 translation of the Python AST to lean.
see: https://docs.python.org/3/library/ast.html
-/

namespace KLR.Python

structure Pos where
  lineno : Nat := 0
  end_lineno : Nat := 0
  col_offset : Nat := 0
  end_col_offset : Nat := 0
  deriving Repr

inductive Const where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | float (value : Float)
  | string (value : String)
  | ellipsis
  deriving Repr

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

inductive Ctx where
  | load | store | del
  deriving Repr

-- Python boolean operators
inductive BoolOp where
  | and | or
  deriving Repr

-- Python comparison operators
inductive CmpOp where
  | eq | ne | lt | le | gt | ge | is | isNot | isIn | notIn
  deriving Repr

-- Python unary operators
inductive UnaryOp where
  | invert | not | uadd | usub
  deriving Repr

-- Python binary operators
inductive BinOp where
  | add | sub | mul | matmul | div | mod | pow
  | lshift | rshift | or | xor | and
  | floor
  deriving Repr

mutual
inductive Expr where
  | exprPos (expr : Expr') (pos : Pos)
  deriving Repr

inductive Expr' where
  | const (value : Const)
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
  deriving Repr

inductive Keyword where
  | keyword (id : String) (value : Expr) (pos : Pos)
  deriving Repr
end

mutual
inductive Stmt where
  | stmtPos (stmt : Stmt') (pos : Pos)
  deriving Repr

inductive Stmt' where
  | pass
  | expr (e : Expr)
  | assert (e : Expr)
  | ret (e: Expr)
  | assign (xs: List Expr) (e: Expr)
  | augAssign (x : Expr) (op : BinOp) (e : Expr)
  | annAssign (x : Expr) (annotation : Expr) (value : Option Expr)
  | forLoop (x : Expr) (iter: Expr) (body: List Stmt) (orelse : List Stmt)
  | ifStm (e : Expr) (thn els: List Stmt)
  deriving Repr
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
structure Args where
  posonlyargs : List String
  args : List String
  defaults: List Expr'
  vararg : Option String
  kwonlyargs : List String
  kw_defaults: List (String × Expr')
  kwarg : Option String
  deriving Repr

def Args.names (args : Args) : List String :=
  args.posonlyargs ++ args.args ++ args.kwonlyargs

def Args.all_defaults (args : Args) : List (String × Expr') :=
  let pargs := args.posonlyargs ++ args.args
  let dflt  := pargs.reverse.zip args.defaults.reverse
  dflt ++ args.kw_defaults

structure Fun where
  line : Nat
  source : String
  args : Args
  body: List Stmt
  deriving Repr

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
structure Kernel where
  entry : String
  funcs : List (String × Fun)
  args : List Expr'
  kwargs : List (String × Expr')
  globals : List (String × Expr')

-------------------------------------------------------------------------------
-- Converting Python AST from Json

namespace Parsing
open Lean

-- I am using a state monad only to provide better error messages: the source
-- span (Pos) is saved while traversing the tree to identify the location
-- of any errors in the original program

abbrev Parser := StM Pos

private def str : Json -> Parser String :=
  monadLift ∘ Json.getStr?

private def field (f: Json -> Parser a) (j : Json) (name : String) : Parser a :=
  j.getObjVal? name >>= f

private def field? (f: Json -> Parser a) (j : Json) (name : String) : Parser (Option a) :=
  try let x <- field f j name; return (some x)
  catch _ => return none

private def list (f: Json -> Parser a) : Json -> Parser (List a)
  | .arr arr => arr.toList.mapM f
  | json => return [(<- f json )]

private def dict (f : Json -> Parser a) : Json -> Parser (List (String × a))
  | .obj kvs => kvs.toArray.toList.mapM fun p => return (p.1, (<- f p.2))
  | _ => throw s!"expecting dictionary"

private def opt (p : Json -> Parser a) : Json -> Parser (Option a)
  | .null => return none
  | j => return (some (<- p j))

-- Note: this will not fail, but can produce an invalid Pos
private def pos (j: Json) : Parser Pos :=
  return {
    lineno         := (<- nat "lineno")
    end_lineno     := (<- nat "end_lineno")
    col_offset     := (<- nat "col_offset")
    end_col_offset := (<- nat "end_col_offset")
  }
where
  nat (name : String) : Parser Nat :=
    tryCatch (nat' name) fun _ => return 0
  nat' (name : String) : Parser Nat := do
    let obj <- j.getObjVal? name
    Json.getNat? obj

private def withPos (p : String -> Json -> Parser b) (f : b -> Pos -> a) : Json -> Parser a
  | .obj (.node _ _ key val _) => do
    let pos <- pos val
    set pos
    let exp <- p key val
    return (f exp pos)
  | _ => throw "expecting object"

def genError (offset : Nat) (source err : String) (pos : Pos) : String :=
  let lines := source.splitOn "\n"
  let lineno := pos.lineno - 1
  let colno := pos.col_offset
  let line := if lines.length < lineno
              then "<source not available>"
              else lines[lineno]!
  let indent := (Nat.repeat (List.cons ' ') colno List.nil).asString
  s!"line {lineno + offset}:\n{line}\n{indent}^-- {err}"

private def withSrc (line : Nat) (source : String) (p : Parser a) : Parser a :=
  try set { lineno := 0 : Pos } ; p
  catch e => do
    let pos <- get
    throw (genError line source e pos)

-------------------------------------------------------------------------------
-- Python AST Json objects

def const : Json -> Parser Const
  | .null => return .none
  | .bool b => return .bool b
  | .num { mantissa := m, exponent := 0 } => return .int m
  | .num jn => return .float jn.toFloat
  | .str "..." => return .ellipsis
  | .str s => return .string s
  | _ => throw "expecting constant"

def exprCtx : Json -> Parser Ctx
  | .str "Load" => return .load
  | .str "Store" => return .store
  | .str "Del" => return .del
  | _ => throw "expecting ctx"

def boolOp (j : Json) : Parser BoolOp := do
  match <- str j with
  | "And" => return .and
  | "Or" => return .or
  | s => throw s!"unknown operator {s}"

def cmpOp (j : Json) : Parser CmpOp := do
  match <- str j with
  | "Eq" => return .eq
  | "NotEq" => return .ne
  | "Lt" => return .lt
  | "LtE" => return .le
  | "Gt" => return .gt
  | "GtE" => return .ge
  | "Is" => return .is
  | "IsNot" => return .isNot
  | "In" => return .isIn
  | "NotIn" => return .notIn
  | s => throw s!"unknown operator {s}"

def unaryOp (j: Json) : Parser UnaryOp := do
  match <- str j with
  | "Invert" => return .invert
  | "Not" => return .not
  | "UAdd" => return .uadd
  | "USub" => return .usub
  | s => throw s!"unknown operator {s}"

def binOp (j: Json) : Parser BinOp := do
  match <- str j with
  | "Add" => return .add
  | "Sub" => return .sub
  | "Mult" => return .mul
  | "MatMult" => return .matmul
  | "Div" => return .div
  | "Mod" => return .mod
  | "Pow" => return .pow
  | "LShift" => return .lshift
  | "RShift" => return .rshift
  | "BitOr" => return .or
  | "BitXor" => return .xor
  | "BitAnd" => return .and
  | "FloorDiv" => return .floor
  | s => throw s!"unknown operator {s}"

partial def expr (j : Json) : Parser Expr :=
  withPos expr' Expr.exprPos j
where
  expr' (key : String) (j : Json) : Parser Expr' := do
    let boolOp := field boolOp j
    let binOp := field binOp j
    let unaryOp := field unaryOp j
    let cmpOps := field (list cmpOp) j
    let str := field str j
    let ctx := field exprCtx j
    let const := field const j
    let exprs := field (list expr) j
    let expr? := field (opt expr) j
    let expr := field expr j
    let keywords := field (list keyword) j
    match key with
    | "Constant" => return (.const (<- const "value"))
    | "Name" => return (.name (<- str "id") (<- ctx "ctx"))
    | "Attribute" => return (.attr (<- expr "value") (<- str "attr") (<- ctx "ctx"))
    | "Tuple" => return (.tuple (<- exprs "elts") (<- ctx "ctx"))
    | "List" => return (.list (<- exprs "elts") (<- ctx "ctx"))
    | "Subscript" => return (.subscript (<- expr "value") (<- expr "slice") (<- ctx "ctx"))
    | "Slice" => return (.slice (<- expr? "lower") (<- expr? "upper") (<- expr? "step"))
    | "BoolOp" => return (.boolOp (<- boolOp "op") (<- exprs "values"))
    | "BinOp" => return (.binOp (<- binOp "op") (<- expr "left") (<- expr "right"))
    | "UnaryOp" => return (.unaryOp (<- unaryOp "op") (<- expr "operand"))
    | "Compare" => return (.compare (<- expr "left") (<- cmpOps "ops") (<- exprs "comparators"))
    | "IfExp" => return (.ifExp (<- expr "test") (<- expr "body") (<- expr "orelse"))
    | "Call" => return (.call (<- expr "func") (<- exprs "args") (<- keywords "keywords"))
    | _ => throw s!"unsupported python construct {key}"

  keyword (j: Json) : Parser Keyword := do
    let j <- j.getObjVal? "keyword"
    return ⟨ <- field str j "arg", <- field expr j "value", <- pos j ⟩

partial def stmt (j : Json) : Parser Stmt :=
  withPos stmt' Stmt.stmtPos j
where
  stmt' (key : String) (j : Json) : Parser Stmt' := do
    let binOp := field binOp j
    let exprs := field (list expr) j
    let expr? := field (opt expr) j
    let expr := field expr j
    let stmts := field (list stmt) j
    match key with
    | "Pass" => return .pass
    | "Expr" => return (.expr (<- expr "value"))
    | "Assert" => return (.assert (<- expr "test"))
    | "Return" => return (.ret (<- expr "value"))
    | "Assign" => return (.assign (<- exprs "targets") (<- expr "value"))
    | "AugAssign" => return (.augAssign (<- expr "target") (<- binOp "op") (<- expr "value"))
    | "AnnAssign" => return (.annAssign (<- expr "target") (<- expr "annotation") (<- expr? "value"))
    | "For" => return (.forLoop (<- expr "target") (<- expr "iter") (<- stmts "body") (<- stmts "orelse"))
    | "If" => return (.ifStm (<- expr "test") (<- stmts "body") (<- stmts "orelse"))
    | _ => throw s!"unsupported python construct {key}"

-- Both global references and arguments are processed in the global
-- environment. These terms do not have a position, and must be
-- evaluable in the default environment.
partial def global : Json -> Parser Expr'
  | .null => return .const .none
  | .obj (.node _ _ "fun"   (.str  s)    _) => return .name s .load
  | .obj (.node _ _ "mod"   (.str  s)    _) => return .name s .load
  | .obj (.node _ _ "bool"  (.bool b)    _) => return .const (.bool b)
  | .obj (.node _ _ "float" (.num  n)    _) => return .const (.float n.toFloat)
  | .obj (.node _ _ "int"   (.num ⟨m,0⟩) _) => return .const (.int m)
  | .obj (.node _ _ "str"   (.str s)     _) => return .const (.string s)
  | .obj (.node _ _ "tuple" (.arr arr)   _) => return .tuple (<- globals arr) .load
  | .obj (.node _ _ "list"  (.arr arr)   _) => return .list  (<- globals arr) .load
  | .obj (.node _ _ "tensor" kvs         _) => do
      let dtype <- field global kvs "dtype"
      let shape <- field global kvs "shape"
      match dtype, shape with
      | .const (.string s), .tuple l _ => return .tensor l s
      | _, _ => throw "malformed tensor type"
  | j => throw s!"malformed global environment '{j}'"
where
  globals (arr : Array Json) : Parser (List Expr) :=
    arr.toList.mapM fun x => return .exprPos (<- global x) {}

def arguments (j : Json) : Parser Args := do
  let obj <- j.getObjVal? "arguments"
  return {
    posonlyargs := (<- field (list arg)    obj "posonlyargs")
    args        := (<- field (list arg)    obj "args")
    defaults    := (<- field (list global) obj "defaults")
    vararg      := (<- field (opt arg)     obj "vararg")
    kwonlyargs  := (<- field (list arg)    obj "kwonlyargs")
    kw_defaults := (<- field (dict global) obj "kw_defaults")
    kwarg       := (<- field (opt arg)     obj "kwarg")
  }
where
  arg (j : Json) : Parser String := do
    let obj <- j.getObjVal? "arg"
    return (<- field str obj "arg")

def function (j : Json) : Parser Fun := do
  let line <- j.getObjValAs? Nat "line"
  let source <- field str j "source"
  withSrc line source do
    let args <- field arguments j "args"
    let body <- field (list stmt) j "body"
    return Fun.mk line source args body

def kernel (j : Json) : Parser Kernel := do
  let name <- field str j "entry"
  let funcs <- field (dict function) j "funcs"
  let args <- field (list global) j "args"
  let kwargs <- field (dict global) j "kwargs"
  let globals <- field (dict global) j "globals"
  return Kernel.mk name funcs args kwargs globals

def parse (s : String) : Err Kernel := do
  let jsn <- Json.parse s
  match kernel jsn {} with
  | .ok x _ => .ok x
  | .error s _ => .error s
