/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.Memory

def List.dot [Mul α] [Add α] [Zero α] (L1 L2 : List α) : α :=
  (List.zipWith (· * ·) L1 L2).sum

class Encodable (dsize : Nat) (α β : Type _) where
  read : Vector α dsize → Option β
  write : β → Vector α dsize
  read_write : (read v).map write = .none ∨ (read v).map write = .some v
  write_read : read (write b) = .some b

def Dtype.interp {DataT : Type _} : KLR.Core.Dtype → Type
| .uint64   => UInt64
| .uint32   => UInt32
| .uint16   => UInt16
| .uint8    => UInt8
| .int64    => Int64
| .int32    => Int32
| .int16    => Int16
| .int8     => Int8
| .float16 | .float32r | .float32 | .float8e5 | .float8e4 | .float8e3 | .bfloat16 => DataT

namespace NML

/-
# NML, Neuron Modeling Language

Plan:
The language contains a subset that is similar to the ISA, but abstracts over the lowest-level details.
The langauge contains a subset similar to some of the higher-level operators akin to KLR, or `nki.language`.
Finally, it contains ghost operations that are purely logical and have no concrete meaning in either
language, such as the unbounded allocation operator.
Like several other relational logics, this setup allows users to prove chains of equivalences where
the intermediate programs are not constrained to any individual language.
For us, this is enabled by the fact that all of our languages are very similar, and can all fit into a single
operational semantics.

The language is parameterized by a type of floating point numbers, see `KLR/Semantics/Float.lean` -/

section ModelProgram

variable (DataT : Type _)

/-- A multiaffine equation describing an access into a free coordinate of an Address -/
structure AccessV where
  free_offset : Int
  free_strides : List Int
  par_offset : Int
  par_stride : Int
  deriving Repr, BEq

def AccessV.par (a : AccessV) (i : Int) : Int :=
  a.par_offset + a.par_stride * i

def AccessV.free (a : AccessV) (i : List Int) : Int :=
  a.free_offset + List.dot a.free_strides i

/-- Values
The "data" field represetns the type of data in our tensors, which the semantics is
parametric with respect to. Control flow should not depend on data. -/
inductive Value
| var : String → Value
| bool : Bool → Value
| data : DataT → Value
| int : Int → Value
| access : AccessV → Value
  deriving Repr, BEq

inductive Expr where
| value (v : Value DataT)
| call (f : String) (args : List (Value DataT)) (kwargs : List (String × (Value DataT)))
  deriving Repr, BEq

inductive Stmt
| ret (v : Value DataT)
| assign (x : String) (e : Expr DataT)

--   | store (dst : Access) (op : Operator) (args : List Value)

/-- A program is either running through a list of statements, or is terminated with a value. -/
inductive Program where
| run : List (Stmt DataT) → Program
| done : Value DataT → Program

end ModelProgram

section ModelSemantics

open KLR.Core

variable (DataT : Type _)

def Dtype.interp : Dtype → Type _
| .uint64   => UInt64
| .uint32   => UInt32
| .uint16   => UInt16
| .uint8    => UInt8
| .int64    => Int64
| .int32    => Int32
| .int16    => Int16
| .int8     => Int8
| .float16 | .float32r | .float32 | .float8e5 | .float8e4 | .float8e3 | .bfloat16 => DataT

/-- A tensor that has been both allocated in and laid out in memory.

TensorName ensures that the tensor must fit inside the Address, but not necessarily how it's laid out.
-/
structure RuntimeTensor extends KLR.Core.TensorName where
  /-- Interpret vectors of store-level indicies into -/
  [encoding : Encodable dtype.size UInt8 (Dtype.interp DataT dtype) ]
  /-- Where the tensor is being stored in our memory model -/
  index : DualMemoryStoreIndex UInt8
  /-- Multiaffine equation mapping tensor indices to Address indices (not physical)! -/
  layout : AccessV

/-- State of the program.
Currently, there is one core's-worth of memory.
We won't do a substitution-based semantics, we will store local variables in the Allocs field.  -/
structure State where
  memory : NeuronMemory
  allocs : Array (RuntimeTensor DataT)

structure Cfg where
  program : Program DataT
  state : State DataT

/-- Small step semantics
Written this way to support nondeterminisim, however, the modelling language is currently deterministic.

A program is stuck when it cannot take a step. -/
inductive Step : Cfg DataT → Cfg DataT → Type _ where
| ret : Step ⟨.run [.ret v], s⟩ ⟨.done v, s⟩

/-- The type of traces that terminate without getting stuck. -/
inductive Trace : Cfg DataT → Cfg DataT → Type _ where
| term : Trace ⟨.done v, s⟩ ⟨.done v, s⟩
| step : Step DataT c1 c2 → Trace c2 c3 → Trace c1 c3


end ModelSemantics
end NML
