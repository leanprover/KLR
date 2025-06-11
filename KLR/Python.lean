/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Serde.Attr
import KLR.Util

/-!
# Abstract syntax of Python functions

Mostly 1-to-1 translation of the Python AST to lean.
see: https://docs.python.org/3/library/ast.html
-/

namespace KLR.Python

@[serde tag = 1]
structure Pos where
  lineno : Nat := 0
  end_lineno : Nat := 0
  col_offset : Nat := 0
  end_col_offset : Nat := 0
  deriving Repr, BEq

@[serde tag = 2]
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

@[serde tag = 3]
inductive Ctx where
  | load | store | del
  deriving Repr

-- Python boolean (logical) operators
@[serde tag = 4]
inductive BoolOp where
  | land | lor
  deriving Repr

-- Python comparison operators
@[serde tag = 5]
inductive CmpOp where
  | eq | ne | lt | le | gt | ge | is | isNot | isIn | notIn
  deriving Repr

-- Python unary operators
@[serde tag = 6]
inductive UnaryOp where
  | invert | not | uadd | usub
  deriving Repr

-- Python binary operators
@[serde tag = 7]
inductive BinOp where
  | add | sub | mul | matmul | div | mod | pow
  | lshift | rshift | or | xor | and
  | floor -- the '//' operator in Python
  deriving Repr

mutual
@[serde tag = 8]
structure Expr where
  expr : Expr'
  pos : Pos
  deriving Repr

@[serde tag = 9]
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
  deriving Repr

@[serde tag = 10]
structure Keyword where
  id : String
  value : Expr
  pos : Pos
  deriving Repr
end

mutual
@[serde tag = 11]
structure Stmt where
  stmt : Stmt'
  pos : Pos
  deriving Repr

@[serde tag = 12]
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
@[serde tag = 13]
structure Args where
  posonlyargs : List String
  args : List String
  defaults: List Expr
  vararg : Option String
  kwonlyargs : List String
  kw_defaults: List Keyword
  kwarg : Option String
  deriving Repr

def Args.names (args : Args) : List String :=
  args.posonlyargs ++ args.args ++ args.kwonlyargs

-- TODO: does not compute required keyword args
def Args.required (args : Args) : List String :=
  let pargs := args.posonlyargs ++ args.args
  pargs.take (pargs.length - args.defaults.length)

def Args.all_defaults (args : Args) : List Keyword :=
  let pargs := args.posonlyargs ++ args.args
  let dflt  := pargs.reverse.zip args.defaults.reverse
  let dflt  := dflt.map fun (n, e) => .mk n e {}
  dflt ++ args.kw_defaults

@[serde tag = 14]
structure Fun where
  name : String
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
instance : Repr Lean.Json where
  reprPrec jsn _ := jsn.compress

@[serde tag = 15]
structure Kernel where
  entry : String
  funcs : List Fun
  args : List Expr
  kwargs : List Keyword
  globals : List Keyword
  undefinedSymbols : List String
  deriving Repr

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
    let ten := { expr := .const (.int 10), pos := {} }
    let dtype := "nki.language.float32"
    let tensors := args.map fun _ => { expr := .tensor [ten,ten] dtype, pos := {} }
    return tensors

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

private def json (jsn : Json) : Parser Json := return jsn

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
  s!"\nline {lineno + offset}:\n{line}\n{indent}^-- {err}"

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
  | "And" => return .land
  | "Or" => return .lor
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
  withPos expr' Expr.mk j
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
  withPos stmt' Stmt.mk j
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
    | "If" => return (.ifStm (<- expr "test") (<- stmts "body") (<- stmts "orelse"))
    | "For" => return (.forLoop (<- expr "target") (<- expr "iter") (<- stmts "body") (<- stmts "orelse"))
    | "Break" => return .breakLoop
    | "Continue" => return .continueLoop
    | _ => throw s!"unsupported python construct {key}"

-- Both global references and arguments are processed in the global
-- environment. These terms do not have a position, and must be
-- evaluable in the default environment.
partial def global' : Json -> Parser Expr'
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
      let dtype <- field global' kvs "dtype"
      let shape <- field global' kvs "shape"
      match dtype, shape with
      | .const (.string s), .tuple l _ => return .tensor l s
      | _, _ => throw "malformed tensor type"
  | j => throw s!"malformed global environment '{j}'"
where
  globals (arr : Array Json) : Parser (List Expr) :=
    arr.toList.mapM fun x => return .mk (<- global' x) {}

private def global (j : Json) : Parser Expr :=
  return { expr := <- global' j, pos := {} }

def arguments (j : Json) : Parser Args := do
  let obj <- j.getObjVal? "arguments"
  let kws <- field (dict global) obj "kw_defaults"
  let kws := kws.map fun (n,e) => Keyword.mk n e {}
  return {
    posonlyargs := (<- field (list arg)    obj "posonlyargs")
    args        := (<- field (list arg)    obj "args")
    defaults    := (<- field (list global) obj "defaults")
    vararg      := (<- field (opt arg)     obj "vararg")
    kwonlyargs  := (<- field (list arg)    obj "kwonlyargs")
    kw_defaults := kws
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
    return Fun.mk "" line source args body

def kernel (j : Json) : Parser Kernel := do
  let name <- field str j "entry"
  let funcs <- field (dict function) j "funcs"
  let funcs := funcs.map fun (name,f) => { f with name }
  let args <- field (list global) j "args"
  let kwargs <- field (dict global) j "kwargs"
  let kwargs := kwargs.map fun (n,e) => Keyword.mk n e {}
  let globals <- field (dict global) j "globals"
  let globals := globals.map fun (n,e) => Keyword.mk n e {}
  let undefinedSymbols <- field (list str) j "undefined_symbols"
  let undefinedSymbols := undefinedSymbols.eraseDups
  return Kernel.mk name funcs args kwargs globals undefinedSymbols

def parse (s : String) : Err Kernel := do
  let jsn <- Json.parse s
  match kernel jsn {} with
  | .ok x _ => .ok x
  | .error s _ => .error s
