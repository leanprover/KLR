/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import ISA.Basic
import ISA.Simplify
import KLR.Util

namespace ISA.Parser
open KLR (Err StM)

/-
These definitions mirror the Rust types and are designed
to make interop between Lean's FromJson and rust's serde_json
as automatic as possible.
-/

inductive IntType where
  | u8 | u16 | u32 | u64
  deriving Lean.FromJson

inductive ExprOp where
  | Period        -- .
  | Equal         -- ==
  | NotEqual      -- !=
  | IfElse        -- If()then{}else{}
  | Gt            -- >
  | Lt            -- <
  | Gte           -- >=
  | Lte           -- <=
  | Plus          -- +
  | Minus         -- -
  | As            -- as
  | Multiply      -- *
  | Divide        -- /
  | Modulo        -- %
  | ShiftLeft     -- <<
  | ShiftRight    -- >>
  | BitwiseInvert -- ~
  | BitwiseOr     -- |
  | BitwiseAnd    -- &
  | BitwiseXor    -- ^
  | LogicalInvert -- !
  | LogicalOr     -- ||
  | LogicalAnd    -- &&
  deriving Repr, Lean.FromJson

-- Note: the IntType of Int is inconsistent and is ignored: e.g. Int u8 1024
inductive RustExpr where
  | Int (type : IntType) (value : Int)  -- 3
  | Path (components : List String)     -- a.b
  | Index (expr index : RustExpr)       -- a[1]
  | Unary (op : ExprOp) (e : RustExpr)  -- !e
  | Binary (op : ExprOp) (left right : RustExpr)  -- a + b
  | Ternary (op : ExprOp) (cond thn els : RustExpr) -- c ? thn : els
  | Call (f : RustExpr) (args : List RustExpr) -- f(args)
  | Group (e : RustExpr) -- (e)
  | List (op : ExprOp) (exps : List RustExpr) -- unused

-- Rust encodes tuples as lists, and Lean encodes tuples as nested pairs
-- Manual instance seems easiest way
-- Note: partial due to mapM

partial def RustExpr.fromJson? : Lean.Json -> Err RustExpr
  | .obj (.node _ _ "Binary" (.arr #[a,b,c]) _) =>
    return .Binary (<- Lean.fromJson? a) (<- fromJson? b) (<- fromJson? c)
  | .obj (.node _ _ "Index" (.arr #[a,b]) _) =>
    return .Index (<- fromJson? a) (<- fromJson? b)
  | .obj (.node _ _ "Ternary" (.arr #[a,b,c,d]) _) =>
    return .Ternary (<- Lean.fromJson? a) (<- fromJson? b) (<- fromJson? c) (<- fromJson? d)
  | .obj (.node _ _ "Unary" (.arr #[a,b]) _) =>
    return .Unary (<- Lean.fromJson? a) (<- fromJson? b)
  | .obj (.node _ _ "Group" j _) =>
    return .Group (<- fromJson? j)
  | .obj (.node _ _ "Int" j _) => do
    let ty <- j.getObjValAs? IntType "inttype"
    let val <- j.getObjValAs? _ "value"
    return .Int ty val
  | .obj (.node _ _ "Path" (.obj (.node _ _ "components" j _)) _) =>
    return .Path (<- Lean.fromJson? j)
  | .obj (.node _ _ "List" (.arr #[a,.arr b]) _) =>
    return .List (<- Lean.fromJson? a) (<- b.toList.mapM fromJson?)
  | .obj (.node _ _ "Call" (.arr #[a,.arr b]) _) =>
    return .Call (<- fromJson? a) (<- b.toList.mapM fromJson?)
  | _ => throw "expecting RustExpr"

instance : Lean.FromJson RustExpr := ⟨ RustExpr.fromJson? ⟩

-- many more token types are defined, but only comments
-- make it into the final parsed output
inductive TokenType where
  | CommentSingleLine : String -> TokenType
  deriving Lean.FromJson

-- Note: ignoring positions: start and end
structure Token where
  ttype : TokenType
  deriving Lean.FromJson

structure EnumEntry where
  name : String
  value : RustExpr
  comment : List Token
  deriving Lean.FromJson

structure StructAttributeInfo where
  is_inst : Bool
  opcodes : Option (List String)
  deriving Lean.FromJson

structure StructEntry where
  name : String
  stype : String
  isvec : Bool
  number : RustExpr
  comment : List Token
  deriving Lean.FromJson

structure StructInfo where
  name : String
  attributes : StructAttributeInfo
  entries : List StructEntry
  comment : List Token
  deriving Lean.FromJson

-- This corresponds to StructItem.stype, FunctionType, and IntType in rust

private def typFromString : String -> Err Typ
  | "bool" => return .bool
  | "u8" => return .u8
  | "u16" => return .u16
  | "u32" => return .u32
  | "usize" => return .usize
  | "i8" => return .i8
  | "i16" => return .i16
  | "i32" => return .i32
  | "Inst" => return .inst
  | s => throw s!"expecting type got {s}"

private def typOfString (s : String) : Typ :=
  match typFromString s with
  | .ok t => t
  | .error _ => .named s

instance : Lean.FromJson Typ where
  fromJson?
  | .str s => typFromString s
  | .obj (.node _ _ "Other" (.str s) _) => return .named s
  | _ => throw "expecting Type"

structure FunctionAttributeInfo where
  gen_c:          Bool
  gen_z3:         Bool
  gen_rust:       Bool
  gen_sv:         Bool
  dbgok:          Bool
  manual_dbg_gen: Bool
  z3arith:        Bool
  deriving Lean.FromJson

structure FunctionArg where
  name : String
  arg_type : Typ
  deriving Lean.FromJson

structure FunctionInfo where
  name : String
  attributes : FunctionAttributeInfo
  arguments : List FunctionArg
  return_type : Typ
  expression : RustExpr
  deriving Lean.FromJson

inductive ParseItem where
  | ConstantItem (name : String) (value : RustExpr) (comment : List Token)
  | FilePathItem (path : String)
  | TypeItem (name : String) (type_ref : String) (comment : List Token)
  | EnumItem (name : String) (entries : List EnumEntry) (comment : List Token)
  | StructItem : StructInfo -> ParseItem
  | BStructItem : StructInfo -> ParseItem
  | UnionItem (name : String) (entries : List StructEntry) (comment : List Token)
  | AssertionGroupItem (name : String) (functions : List FunctionInfo)
  | CommentItem (comment : List Token)
  | AttributeItem (attribute_text : String)
  | RawRust (rust_string : String)
  | RawZ3 (z3_string : String)
  | RawC (c_string : String)
  | RawCFwd (c_string : String)
  | RawSV (sv_string : String)
  deriving Lean.FromJson

structure ISAFile where
  name : String
  items : List ParseItem

/-
# Parsing / Translation to types in ISA.Basic

Parse Json and translate "rust types" to types in Lean. This code simplifies
some aspects of the types and checks some invariants that (I believe) should be
true.
-/

structure State where
  file : String := ""
  instNames : Env String := default
  current : Option InstFormat := none
  block : Option String := none
  group : Env Function := ∅
  isa : ISA := { }

abbrev Simp := StM State

def reset (file : String) : Simp Unit :=
  modify fun s => { s with
    file
    current := none
    block := none
    group := ∅
  }

def modifyM (f : State -> Err State) : Simp Unit := do
  set (<- f (<- get))

def setCurrent (name : String) (ops : List String) : Simp Unit := do
  let s <- get
  if s.current.isSome then
    throw s!"Multiple instruction formats in file {s.file}"
  -- record instruction to format mapping and check for duplicates
  let mut opcs := s.instNames
  for op in ops do
    opcs := <- opcs.addNew op name
  set { s with
        instNames := opcs
        current := some { name, opcodes := ops }
      }

def ignored : List String := [
  -- These instructions are 128 bytes
  "PseudoTriggerCollective2",
  "PseudoDmaDirect2d",
  "PseudoExtension",
  -- customer instructions
  "ExtendedInst",
  ]

def addOpcode (name : String) (maintained : Bool) : Simp Unit :=
  modifyM fun s =>
    return { s with isa.opcodes := <- s.isa.opcodes.addNew name maintained }

def addConst (name : String) (expr : Expr) : Simp Unit :=
  modifyM fun s =>
    match Simplify.simplifyExpr expr { } with
    | .ok (.int i) _ => return { s with isa.consts := <- s.isa.consts.addNew name i }
    | .ok e _ => throw s!"non-constant constant {name} {repr e}"
    | .error s _ => throw s

def addTyp (name : String) (typ : Typ) : Simp Unit :=
  modifyM fun s =>
    return { s with isa.types := <- s.isa.types.addNew name typ }

def addItem (name : String) (item : ISAItem) : Simp Unit :=
  modifyM fun s =>
    return { s with isa.items := <- s.isa.items.addNew name item }

def unop : ExprOp -> Err UnOp
  | .LogicalInvert => return .logicalNot
  | .Minus => return .negate
  | op => throw s!"expecting unop got {repr op}"

def binOp : ExprOp -> Err BinOp
  | .Plus          => return .plus
  | .Minus         => return .minus
  | .Multiply      => return .multiply
  | .Divide        => return .divide
  | .Modulo        => return .modulo
  | .ShiftLeft     => return .shiftLeft
  | .ShiftRight    => return .shiftRight
  | .BitwiseInvert => return .bitwiseInvert
  | .BitwiseOr     => return .bitwiseOr
  | .BitwiseAnd    => return .bitwiseAnd
  | .BitwiseXor    => return .bitwiseXor
  | .LogicalOr     => return .logicalOr
  | .LogicalAnd    => return .logicalAnd
  | op => throw s!"expecting binop got {repr op}"

def cmpOp : ExprOp -> Err CmpOp
  | .Equal    => return .eq
  | .NotEqual => return .ne
  | .Gt       => return .gt
  | .Lt       => return .lt
  | .Gte      => return .ge
  | .Lte      => return .le
  | op => throw s!"expecting cmpop got {repr op}"

def binOrCmpOp (op : ExprOp) : Err (Sum BinOp CmpOp) := do
  try return .inr (<- cmpOp op)
  catch _ => return .inl (<- binOp op)

def expr : RustExpr -> Err Expr
  | .Int _ i => return .int i
  | .Path [] => throw "invalid empty path"
  | .Path l => return .var (l.foldl .str .anonymous)
  | .Index e i => return .index (<- expr e) (<- expr i)
  | .Unary op e => return .unop (<- unop op) (<- expr e)
  | .Binary .Period l r => do
      match <- expr l, <- expr r with
      | .var l, .var r => return .var (l.appendCore r)
      | .var l, .index (.var r) e => return .index (.var $ l.appendCore r) e
      | l, r => return .proj l r
  | .Binary .As e t => do
      let e <- expr e
      match <- expr t with
      | .var `u8 => return .cast e 8
      | .var `u16 => return .cast e 16
      | .var `u32 => return .cast e 32
      | .var `i16 => return .cast e 16 (signed := true)
      | .var `i32 => return .cast e 32 (signed := true)
      | .var `RegNum => return .cast e 8
      | .var `PartitionOffset => return .cast e 32
      | e => throw s!"expecting integral type in cast, got {repr e}"
  | .Binary op l r => do
      match <- binOrCmpOp op with
      | .inl op => return .binop op (<- expr l) (<- expr r)
      | .inr op => return .cmp op (<- expr l) (<- expr r)
  | .Ternary .IfElse c t e => return .cond (<- expr c) (<- expr t) (<- expr e)
  | .Ternary .. => throw "invalid ternary op"
  | .Call f args => do
      match <- expr f with
      | .var n => return .call n (<- args.attach.mapM fun ⟨a,_⟩ => expr a)
      | e => throw s!"function is not a constant {repr e}"
  | .Group e => expr e
  | .List .. => throw "found list of expressions"

-- A bit scary: extracting information from comment lines
def isMaintained (comments : List Token) : Bool :=
  match comments with
  | [] => true
  | { ttype := .CommentSingleLine s } :: cs =>
    if s.take 5 == "// n," then
      false
    else isMaintained cs

def enum (name : String) (entries : List EnumEntry) : Simp Unit := do
  if name == "Opcode" then
    for e in entries do
      addOpcode e.name (isMaintained e.comment)

  let entry e := return (e.name, <- expr e.value)
  addItem name (.enum name (<- entries.mapM entry))

def structEntry (se : StructEntry) : Simp (String × Typ) := do
  if !se.isvec then
    return (se.name, .named se.stype)

  -- process vector type
  let n <- match se.number with
           | .Int _ (.ofNat n) => pure n
           | _ => throw "expecting number in vector type"
  return (se.name, .vec (.named se.stype) n)

def struct (s : StructInfo) : Simp Unit := do
  let entries <- s.entries.mapM structEntry
  if s.attributes.is_inst then
    let ops := s.attributes.opcodes.get!.eraseDups.removeAll ignored
    setCurrent s.name ops
  addItem s.name (.struct s.name entries)

def union (name : String) (entries : List StructEntry) : Simp Unit := do
  let entries <- entries.mapM structEntry
  addItem name (.union name entries)

-- Note: we assume first function is the top of the call graph
-- TODO: check this is the case
def function (f : FunctionInfo) : Simp Unit := do
  if f.attributes.gen_rust == false then
    return ()
  let expr <- expr f.expression
  let f := {
    name := f.name
    args := f.arguments.map fun a => (a.name, a.arg_type)
    ret  := f.return_type
    expr := expr
  }
  let s <- get
  match s.current with
  | some fmt => do
      let checks <- fmt.checks.addNew f.name f
      let fmt :=
        if fmt.entry.isNone
        then { fmt with checks := checks, entry := some f.name }
        else { fmt with checks := checks }
      set { s with current := some fmt }
  | none => do
      let common <- s.isa.common.addNew f.name f
      set { s with isa := { s.isa with common := common } }

def assertion (name : String) (funs : List FunctionInfo) : Simp Unit := do
  let s <- get
  if s.block.isSome then
    throw "multiple assertion blocks in file {s.file}"
  set { s with block := name }
  funs.forM function
  let s <- get
  if let some cur := s.current then
    let insts <- s.isa.insts.addNew (s.file ++ "." ++ name) cur
    set { s with isa := { s.isa with insts := insts } }

def parseItem : ParseItem -> Simp Unit
  | .ConstantItem name e _ => do addConst name (<- expr e)
  | .FilePathItem .. => throw "found file path item"
  | .TypeItem name ty _ => addTyp name (typOfString ty)
  | .EnumItem name l _ => enum name l
  | .StructItem s
  | .BStructItem s => struct s
  | .UnionItem name es _ => union name es
  | .AssertionGroupItem name funs => assertion name funs
  | .CommentItem ..
  | .AttributeItem ..
  | .RawRust ..
  | .RawZ3 ..
  | .RawC ..
  | .RawCFwd ..
  | .RawSV .. => return ()

def files (files : Array ISAFile) : Simp Unit :=
  files.toList.forM fun f =>
    do reset f.name; f.items.forM parseItem

def translate (version : Nat) (fs : Array ISAFile) : Err ISA :=
  match (files fs).run {} with
  | .error s _ => throw s
  | .ok _ s => return { s.isa with version := version }
