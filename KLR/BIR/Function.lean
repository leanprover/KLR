/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
-/
import Lean
import KLR.Util
import KLR.BIR.Instruction
import KLR.BIR.Instructions

/-
Definitions of container and function types.

This file contains type definitions not generated automatically.

Note: the naming of fields is carefully designed so that the derived
instances of to- and from-json are compatible with the compiler.
-/
namespace KLR.BIR

inductive StorageKind where
  | memory_location_set
  | memory_location
  | register
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

inductive TensorKind where
  | ExternalInput
  | ExternalInputParameter
  | Input
  | ExternalOutput
  | ExternalOutputParameter
  | Output
  | Const
  | Internal
  | Pointer
  | InternalInterface
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

inductive TensorClass where
  | Tensor
  | LoopTensor
  | SingleValueTensor
  | NeuronTensor
  | NeuronWeightTensor
  | IdentityWeightTensor
  | NeuronBlockTensor
  | DRAM2DBlockTensor
  | Neuron3DBlockTensor
  | DRAM3DBlockTensor
  | NeuronLocalTensor
  | NeuronSBTensor
  | NeuronPSUMTensor
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

inductive AddrSpace where
  | Local | Shared
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

inductive MemoryType where
  | Unallocated
  | Input
  | Output
  | DRAM
  | SB
  | PSUM
  | RNGSTATE
  | REG
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure MemoryLocation where
  Skind : StorageKind := .memory_location
  name : String
  type : MemoryType
  addr : Nat := 0   -- per-partition offset
  dims : List Nat   -- num partitions, bytes per partition
  bank : Nat := 0   -- bank id
  base : Nat := 0   -- base partition (0, 32, 64)
  allocated : Option Bool := some false
  pinned : Bool := false
  tensor_id : Option Nat := some 0
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure Allocation where
  Skind : StorageKind := .memory_location_set
  addr_space : Option AddrSpace
  dtype : Option Dtype
  partition_dim : Option Nat
  tensor_shape : List Nat
  name : String
  --no_spill : Option Bool := none  -- should be do_not_spill?
  --volatile : Bool := False        -- unused by walrus?
  --virtual : Option Bool := none
  kind : TensorKind
  --tensor_class : Option TensorClass := none
  memorylocations : List MemoryLocation
  tensorId2MemLocSize : Nat := memorylocations.length
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure Axis where
  name : String
  lb : Nat := 0
  ub : Nat := 0
  stride : Nat := 0
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

/-
Loops contains blocks which contain instructions or loops.

So, we need to tie the knot with this little mutual block. A Loop is
structured very mush like an instruction in BIR, but here we use a
small inductive type which can hold either a loop or an instruction.
-/
mutual
inductive InstLoop where
  | I : Inst -> InstLoop
  | L : Loop -> InstLoop
  deriving BEq, Repr

structure Block where
  name : String
  instructions : List InstLoop
  deriving BEq, Repr

structure Loop where
  opcode : String := "Loop"
  axis : Axis
  blocks : List Block
  deriving BEq, Repr
end

mutual

partial def InstLoop.toJson : InstLoop -> Lean.Json
  | .I i => Lean.toJson i
  | .L l => l.toJson

partial def Block.toJson (b : Block) : Lean.Json :=
  let l := b.instructions.map InstLoop.toJson
  .mkObj [
    ("name", .str b.name),
    ("instructions", .arr (.mk l)) ]

partial def Loop.toJson (loop : Loop) : Lean.Json :=
  let axis := Lean.toJson loop.axis
  let blocks := loop.blocks.map Block.toJson
  .mkObj [
    ("opcode", .str "Loop"),
    ("LoopAxis", axis),
    ("blocks", .arr (.mk blocks)) ]

end

instance : Lean.ToJson InstLoop where toJson := InstLoop.toJson
instance : Lean.ToJson Block where toJson := Block.toJson
instance : Lean.ToJson Loop where toJson := Loop.toJson

mutual

/-
Loops are instructions in BIR, but, as noted above, we have broken
this pattern by using an inductive. So, we have to fix-up the Json
parser to match.
-/
partial def InstLoop.fromJson? (j : Lean.Json) : Err InstLoop := do
  let opcode <- j.getObjValAs? String "opcode"
  match opcode with
  | "Loop" => return .L (<- Loop.fromJson? j)
  | _ => return .I (<- Lean.fromJson? j)

partial def Block.fromJson? (j : Lean.Json) : Err Block := do
  let name <- j.getObjValAs? String "name"
  let insts := j.getObjValD "instructions"
  let insts <- insts.getArr?
  let insts <- insts.toList.mapM InstLoop.fromJson?
  return ⟨ name, insts ⟩

partial def Loop.fromJson? (j : Lean.Json) : Err Loop := do
  let axis <- j.getObjValAs? Axis "LoopAxis"
  let blocks := j.getObjValD "blocks"
  let blocks <- blocks.getArr?
  let blocks <- blocks.toList.mapM Block.fromJson?
  return { axis := axis, blocks := blocks }

end

instance : Lean.FromJson InstLoop where fromJson? := InstLoop.fromJson?
instance : Lean.FromJson Block where fromJson? := Block.fromJson?
instance : Lean.FromJson Loop where fromJson? := Loop.fromJson?

structure FunAttributes where
  need_unroll : Option Bool := some true
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure Function where
  name : String
  attributes : FunAttributes := { }
  allocations : List Allocation
  blocks : List Block
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure Attributes where
  neuron_core_id : Option Nat := some 0
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

structure BIR where
  attributes : Attributes := { }
  functions: List Function
  arch : String := "gen3"
  version : Nat := 2
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson
