/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Util
import Lean

namespace ISA
export KLR (Err StM)
export Lean (Name RBMap)

instance : MonadLift Err IO where
  monadLift
    | .ok x => return x
    | .error s => throw $ .userError s

deriving instance Ord for Name

/-
These types represent the abstract syntax of the arch spec files.
-/

inductive UnOp where
  | logicalNot
  | negate
  deriving Repr, BEq

inductive BinOp where
  | bitwiseInvert
  | bitwiseOr
  | bitwiseAnd
  | bitwiseXor
  | divide
  | logicalOr
  | logicalAnd
  | minus
  | modulo
  | multiply
  | plus
  | shiftLeft
  | shiftRight
  deriving Repr, BEq

def BinOp.commutes : BinOp -> Bool
  | .bitwiseOr | .bitwiseAnd | .bitwiseXor
  | .logicalOr | .logicalAnd
  | .multiply | .plus => true
  | _ => false

inductive CmpOp where
  | eq | ne | ge | gt | le | lt
  deriving Repr, BEq

inductive Typ where
  | bool
  | u8 | u16 | u32 | usize
  | i8 | i16 | i32
  | inst   -- the union of all instructions
  | vec (t : Typ) (size : Nat)  -- [t;n]  Rust-like vector
  | named (name : String)
  deriving Repr, BEq

inductive Expr where
  | int (value : Int)
  | var (v : Name)
  | cast (expr : Expr) (bits : Nat) (signed : Bool := false)
  | proj (left right : Expr)
  | index (left right : Expr)
  | unop (op : UnOp) (expr : Expr)
  | binop (op : BinOp) (left right : Expr)
  | cmp (op : CmpOp) (left right : Expr)
  | cond (cond thn els : Expr)
  | call (f : Name) (args : List Expr)
  deriving Repr, BEq

instance : Inhabited Expr := ⟨ .int 0 ⟩

-- A function body is a single expression
structure Function where
  name : String
  args : List (String × Typ)
  ret  : Typ
  expr : Expr
  deriving Repr, BEq

-- Definitions that need to be converted to Lean
inductive ISAItem where
  | enum (name : String) (variants : List (String × Expr))
  | struct (name : String) (entries : List (String × Typ))
  | union (name : String) (entries : List (String × Typ))
  deriving Repr

-- Containers

abbrev Env a := RBMap String a compare

namespace Env

def addNew (env : Env a) (name : String) (x : a) : Err (Env a) := do
  if env.contains name then
    throw s!"duplicate {name}"
  return env.insert name x

def lookup (env : Env a) (name : String) : Err a :=
  match env.find? name with
  | none => .error s!"{name} not found"
  | some x => .ok x

end Env

-- A single instruction format, generally everything from a single spec file
-- except for common (which is handled below)
structure InstFormat where
  name : String                       -- format name (e.g. s2d3_ts)
  opcodes : List String               -- list of opcodes with this format
  fields : List (String × Typ) := []  -- fields of format structure
  entry : Option String := none       -- entry verification function
  checks : Env Function := ∅          -- all verification functions in file

-- Set of ISA specs - generall all files in a directory (e.g. v3/*)
structure ISA where
  version : Nat := 0
  opcodes : Env Bool := default     -- elements of Opcode enum
  consts : Env Int := default       -- constants
  types : Env Typ := default        -- type abbreviations
  insts : Env InstFormat := default -- set of instruction formats
  common : Env Function := default  -- common verification functions (shared by all formats)
  items : Env ISAItem := default    -- common items (shared by all formats)

structure ISASpecs where
  v2 : ISA := {}
  v3 : ISA := {}
  v4 : ISA := {}
