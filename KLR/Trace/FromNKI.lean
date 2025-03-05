/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import KLR.Core
import KLR.Trace.Types
import KLR.Util

/-
Typeclass for conversion from NKI representation.
-/

namespace KLR.Trace
open KLR.Core

class FromNKI (a : Type) where
  fromNKI? : Term -> Err a

export FromNKI (fromNKI?)

def fromNKI [FromNKI a] (dflt : a) (t : Term) : a :=
  match fromNKI? t with
  | .ok x => x
  | .error _ => dflt

instance [FromNKI a] : FromNKI (List a) where
  fromNKI?
  | .tuple l | .list l => fromNKI? ▷ l
  | _ => throw "expecting sequence (list or tuple)"

instance [FromNKI a] : FromNKI (Option a) where
  fromNKI?
    | .none => return none
    | e => return some (<- fromNKI? e)

instance : FromNKI Term := ⟨ .ok ⟩

instance : FromNKI Expr where
  fromNKI? t :=
    let err ty := throw s!"{ty} cannot be converted to a KLR term"
    match t with
    | .module _    => err "module"
    | .builtin n _ => return .value (.var n.toString)
    | .source _    => err "function"
    | .none        => err "none"
    | .string _    => err "string"
    | .tuple _     => err "tuple"
    | .list _      => err "list"
    | .ellipsis    => err "ellipsis"
    | .slice _ _ _ => err "slice"
    | .store _ _   => err "store"
    | .expr e _    => return e

instance : FromNKI Value where
  fromNKI? t := do
    match <- fromNKI? t with
    | Expr.value v => return v
    | _ => throw "expecting value"

instance : FromNKI Bool where
  fromNKI?
    | .expr (.value $ .bool b) _ => return b
    | _ => throw "expecting boolean"

instance : FromNKI Int where
  fromNKI?
    | .expr (.value $ .bool true) _ => return 1
    | .expr (.value $ .bool false) _ => return 0
    | .expr (.value $ .int i) _ => return i
    | _ => throw "expecting integer"

instance : FromNKI Nat where
  fromNKI?
    | .expr (.value $ .bool true) _ => return 1
    | .expr (.value $ .bool false) _ => return 0
    | .expr (.value $ .int (.ofNat n)) _ => return n
    | _ => throw "expecting positive integer"

instance : FromNKI Float where
  fromNKI?
    | .expr (.value $ .float f) _ => return f
    | _ => throw "expecting float"

instance : FromNKI String where
  fromNKI?
    | .string s => return s
    | _ => throw "expecting string"

-- TODO: when new NKI API is settled, rewrite is a nicer way
instance : FromNKI Dtype where
  fromNKI?
    | .expr (.value $ .var name) _
    | .string name =>
      match name with
      -- NKI variants (see table in NKI docs)
      | "nki.language.uint8" => .ok .uint8
      | "nki.language.int8" => .ok .int8
      | "nki.language.uint16" => .ok .uint16
      | "nki.language.int16" => .ok .int16
      | "nki.language.uint32" => .ok .int32
      | "nki.language.int32" => .ok .int32
      | "nki.language.float8e3" => .ok .float8e3
      | "nki.language.float8e4" => .ok .float8e4
      | "nki.language.float8e5" => .ok .float8e5
      | "nki.language.float8_e4m3" => .ok .float8e4
      | "nki.language.float8_e5m2" => .ok .float8e5
      | "nki.language.float16" => .ok .float16
      | "nki.language.bfloat16" => .ok .bfloat16
      | "nki.language.tfloat32" => .ok .float32r  -- TODO check this
      | "nki.language.float32" => .ok .float32
      | "nki.language.bool_" => .ok .uint8
      -- numpy variants
      | "numpy.uint8" => .ok .uint8
      | "numpy.int8" => .ok .int8
      | "numpy.uint16" => .ok .uint16
      | "numpy.int16" => .ok .int16
      | "numpy.uint32" => .ok .uint32
      | "numpy.int32" => .ok .int32
      | "numpy.float16" => .ok .float16
      | "numpy.float32" => .ok .float32
      | "numpy.bool" => .ok .uint8
      -- imported and string variants
      | "uint8" => .ok .uint8
      | "int8" => .ok .int8
      | "uint16" => .ok .uint16
      | "int16" => .ok .int16
      | "uint32" => .ok .int32
      | "int32" => .ok .int32
      | "float8e3" => .ok .float8e3
      | "float8e4" => .ok .float8e4
      | "float8e5" => .ok .float8e5
      | "float8_e4m3" => .ok .float8e4
      | "float8_e5m2" => .ok .float8e5
      | "float16" => .ok .float16
      | "bfloat16" => .ok .bfloat16
      | "tfloat32" => .ok .float32r  -- TODO check this
      | "float32" => .ok .float32
      | "bool" => .ok .uint8
      | s => throw s!"unsupported dtype {s}"
    | _ => throw s!"expecting dtype"

instance : FromNKI Shape where
  fromNKI? := fromNKI? (a := List Nat)

instance : FromNKI Memory where
  fromNKI? t :=
    let err := .error "expecting buffer type"
    match t with
    | .expr (.value $ .var name) _ =>
      match name with
      -- TODO: do we need to distinguish the different HBM types?
      | "nki.language.shared_hbm" => .ok .dram
      | "nki.language.private_hbm" => .ok .dram
      | "nki.language.hbm" => .ok .dram
      | "nki.language.sbuf" => .ok .sbuf
      | "nki.language.pmem" => .ok .pmem
      | _ => err
    | _ => err

instance : FromNKI Access where
  fromNKI?
    | .expr (.value $ .access a) _ => return a
    | _ => throw "expecting tensor access"

instance : FromNKI TensorName where
  fromNKI?
    | .expr (.value (.access (.simple t))) _ => return t
    | _ => throw "expecting tensor"

instance : FromNKI AluOp where
  fromNKI?
    | .expr (.value $ .var name) _ =>
        match name with
        -- bitwise operations
        | "nki.language.invert" => return .bitwise_not
        | "nki.language.bitwise_and" => return .bitwise_and
        | "nki.language.bitwise_or" => return .bitwise_or
        | "nki.language.bitwise_xor" => return .bitwise_xor
        | "nki.language.left_shift" => return .logical_shift_left
        | "nki.language.right_shift" => return .logical_shift_right
        -- numpy variants
        | "numpy.bitwise_not" => return .bitwise_not
        | "numpy.bitwise_invert" => return .bitwise_not
        | "numpy.bitwise_and" => return .bitwise_and
        | "numpy.bitwise_or" => return .bitwise_or
        | "numpy.bitwise_xor" => return .bitwise_xor
        | "numpy.bitwise_left_shift" => return .logical_shift_left
        | "numpy.bitwise_right_shift" => return .logical_shift_right
        -- arithemetic operations
        | "nki.language.add" => return .add
        | "nki.language.subtract" => return .subtract
        | "nki.language.multiply" => return .mult
        | "nki.language.maximum" => return .max
        | "nki.language.minimum" => return .min
        | "nki.language.equal" => return .is_equal
        | "nki.language.not_equal" => return .not_equal
        | "nki.language.greater_equal" => return .is_ge
        | "nki.language.greater" => return .is_gt
        | "nki.language.less_equal" => return .is_le
        | "nki.language.less" => return .is_lt
        | "nki.language.logical_not" => throw "??"
        | "nki.language.logical_and" => return .logical_and
        | "nki.language.logical_or" => return .logical_or
        | "nki.language.logical_xor" => return .logical_xor
        -- numpy variants
        | "numpy.add" => return .add
        | "numpy.subtract" => return .subtract
        | "numpy.multiply" => return .mult
        | "numpy.maximum" => return .max
        | "numpy.minimum" => return .min
        | "numpy.equal" => return .is_equal
        | "numpy.not_equal" => return .not_equal
        | "numpy.greater_equal" => return .is_ge
        | "numpy.greater" => return .is_gt
        | "numpy.less_equal" => return .is_le
        | "numpy.less" => return .is_lt
        | "numpy.logical_not" => throw "??"
        | "numpy.logical_and" => return .logical_and
        | "numpy.logical_or" => return .logical_or
        | "numpy.logical_xor" => return .logical_xor
        | _ => throw s!"unsupported operator {name}"
    | _ => throw "expecting operator"
