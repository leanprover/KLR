/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import KLR.Core
import KLR.Semantics.Memory
import TensorLib.Iterator

/-
-- TensorLib iterators can't have empty iterators so this is a slight hack
-- Not using option to avoid TC clashes
inductive WithEmpty (I : Type _) where
| nonempty (_ : I)
| empty

-- Probably want a better solution
instance TensorLib.Iterator.WithEmptyIterator [TensorLib.Iterator I V] :
    TensorLib.Iterator (WithEmpty I) (WithEmpty V) where
  next
  | .empty => .none
  | .nonempty i => match @next I V _ i with | .some v => .some (.nonempty v) | .none => .some .empty
  peek
  | .empty => .empty
  | .nonempty i => .nonempty <| peek i
  size
  | .empty => 0
  | .nonempty i => @size I V _ i + 1
  reset _ := .empty
-/


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

/-- A multiaffine equation describing an access into a free coordinate of an Address -/
structure AffineMap where
  free_offset : Int
  free_strides : List Int
  par_offset : Int
  par_stride : Int
  deriving Repr, BEq

def AffineMap.par (a : AffineMap) (i : Int) : Int :=
  a.par_offset + a.par_stride * i

def AffineMap.free (a : AffineMap) (i : List Int) : Int :=
  a.free_offset + List.dot a.free_strides i

def AffineMap.is_trivial (a : AffineMap) : Prop :=
  a.free_offset = 0 ∧
  a.par_offset = 0 ∧
  a.par_stride = 1 ∧
  a.free_strides = a.free_strides.map (fun _ => 1)

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

variable {DataT : Type _}

open KLR.Core

def Dtype.interp : Dtype → Type _
| .uint64   => UInt64
| .uint32   => UInt32
| .uint16   => UInt16
| .uint8    => UInt8
| .int64    => Int64
| .int32    => Int32
| .int16    => Int16
| .int8     => Int8
| .float16 | .float32r | .float32 | .float8e5
| .float8e4 | .float8e3 | .bfloat16 => DataT

/-- A pointer to a tensor that carries additional metadata. -/
structure TensorHandle extends KLR.Core.TensorName where
  /-- Interpret vectors of store-level indicies into -/
  [encoding : Encodable dtype.size UInt8 (Dtype.interp (DataT := DataT) dtype) ]
  /-- Where the tensor is being stored in our memory model -/
  index : KLR.Core.DualMemoryStoreIndex UInt8
  /-- Multiaffine equation mapping tensor indices to Address indices (not physical)! -/
  layout : AffineMap

def TensorHandle.hbm_index? (r : @TensorHandle DataT) : Option Nat :=
  match r.index with
  | .in_bounded => .none
  | .in_unbounded i => .some i

/-- NML values. These are fully-reduced expressions. -/
inductive Value
| bool     (_ : Bool)
| data     (_ : DataT)
| int      (_ : Int)
| linfunc  (_ : AffineMap)
| ptr      (_ : TensorHandle (DataT:=DataT))

def Value.as_handle? : @Value DataT → Option (@TensorHandle DataT) | .ptr t => .some t | _ => .none

/-- NML expressions. These are terms which reduce to a value and possibly update the state.
There is no control flow inside expressions. -/
inductive Expr
| val     (_ : @Value DataT)
| var     (_ : String)
| load    (_ : AffineMap) (_ : Expr)

/-- NML statements. Control flow lives here. -/
inductive Stmt
| ret     (_ : @Expr DataT)
| assign  (_ : Option String) (_ : @Expr DataT)
| loop    (I : Type _) [TensorLib.Iterator I (@Value DataT)] (_ : String) (_ : I) (body : List Stmt)

abbrev Locals := String → Option (@Value DataT)

structure State where
  memory : KLR.Core.NeuronMemory
  locals : @Locals DataT

def Locals.bind (s : @Locals DataT) (x : String) (v : @Value DataT) : @Locals DataT:=
  fun x' => if x = x' then .some v else s x'

/-- The state of execution of the program. -/
inductive ExecState where
| run   (_ : List (@Stmt DataT)) (_ : @State DataT)
| done  (_ : @Value DataT)

/-- Language of expressions.

This is different from KLR's expression lanaguge currently, the semantics should be able to
express something like `nki.load` which is an effectful call that also returns a python-level value. -/
inductive ExprStep : @Expr DataT → @State DataT → @Value DataT → KLR.Core.NeuronMemory → Type _ where
/-- [value] -/
| value :
    ExprStep (.val v) s v s.memory
/-- [variable] -/
| var :
    s.locals x = .some v →
    ExprStep (.var x) s v s.memory
/-- [Non-sized, full, load] Load a HBM tile to a SBUF tile. Return a pointer to the new tile. Similar to nki.load.
For now, only support trivial indexing.
  - Evaluate the location expression to a tensor pointer in hbm
  - Copy the hbm tensor data to a new unbounded tile in sbuf
  - Return the tensor pointer, modified to point at the new sbuf tile -/
| load_full :
    AffineMap.is_trivial asn →
    ExprStep e s (.ptr tensor) s' →
    tensor.address.memory = KLR.Core.Memory.hbm →
    tensor.hbm_index? = .some raw_index →
    (_ : i < s'.hbm.size) →
    ExprStep (.load asn e) s
      (.ptr {tensor with address.memory := .sbuf, index := .in_unbounded s'.sbuf.unbounded.size})
      { s' with sbuf.unbounded := s'.sbuf.unbounded.push s'.hbm[i] }


inductive MultiStep : List (@Stmt DataT) → @State DataT → @ExecState DataT → Type _ where
/-- [ Early return ] Step into the .done state using .ret at any time -/
| ret :
    ExprStep e s v _ →
    MultiStep (.cons (.ret e) ps) s (.done v)
/-- [ Assignment ] Expression evaluates first, with effects. -/
| asn :
    ExprStep e s v s' →
    MultiStep p ⟨s', s.locals.bind x v⟩ r →
    MultiStep (.cons (.assign (.some x) e) p) s r
/-- [ Sequencing ] Evaluate expression but don't bind the result a variable -/
| seq :
    ExprStep e s _ s' →
    MultiStep p ⟨s', s.locals⟩ r →
    MultiStep (.cons (.assign .none e) p) s r
/-- [ Loop termination ] Loops continue onwards if their iterator's next is .none
FIXME: TensorLib.Iterator is wrong for this, need empty iterators. -/
| loop_exit {I : Type _} [TensorLib.Iterator I (@Value DataT)] (i : I) :
    @TensorLib.Iterator.next I (@Value DataT) _ i = .none →
    MultiStep p s r →
    MultiStep (.cons (.loop I _ i _) p) s r
/-- [ Loop eary return ] If loop is not terminated, and body executes to .done, terminate. -/
| loop_early {I : Type _} [TensorLib.Iterator I (@Value DataT)] (i i' : I) :
    (@TensorLib.Iterator.next I (@Value DataT) _ i) = .some i' →
    MultiStep body ⟨s.memory, s.locals.bind x (@TensorLib.Iterator.peek I _ _ i)⟩ (.done r) →
    MultiStep (.cons (.loop I x i body) p) s (.done r)
/-- [ Loop iterate ] If loop is not terminated, and body executes to a running state,
the program setps to a loop with iterator.next (lexical scope + effects). -/
| loop_continue {I : Type _} [TensorLib.Iterator I (@Value DataT)] (i i' : I) :
    (@TensorLib.Iterator.next I (@Value DataT) _ i) = .some i' →
    MultiStep body ⟨s.memory, s.locals.bind x (@TensorLib.Iterator.peek I _ _ i)⟩ (.run [] s') →
    MultiStep (.cons (.loop I x i' body) p) ⟨s'.memory, s.locals⟩ r →
    MultiStep (.cons (.loop I x i body) p) s r

end NML
