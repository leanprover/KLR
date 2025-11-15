import KLR.K.K1.AST
import KLR.K.K2.AST
import KLR.K.Operators
import KLR.Util.Gensym
import Lean
import TensorLib.Tensor

namespace KLR.K.K1

open KLR.TGR(TensorTy)

/- A stack-like allocator that can allocate into a frame and then free that whole frame at once,
but can't free individual allocations. -/
structure StackAllocator where
  /- The set of tops of stack frames, with the base of the current frame at the front -/
  frames : List Nat
  /- The next address to allocate at -/
  offset : Nat
deriving Inhabited, Repr

namespace StackAllocator
/- Allocate a region large enough for `size` elements of type `dtype` in the current frame -/
def alloc (self : StackAllocator) (dtype : Core.Dtype) (size : Nat) : (Nat × StackAllocator) :=
  let bytes := size * dtype.size
  let location := self.offset
  let self := { self with offset := self.offset + bytes }
  (location, self)
/- Start a new frame. -/
def pushFrame (self : StackAllocator) : StackAllocator :=
  { self with frames := self.offset :: self.frames }
/- Free the current frame and pop it from the stack. -/
def popFrame (self : StackAllocator) : StackAllocator :=
  match self.frames with
  | [] => panic "StackAllocator.popFrame: No frames to pop"
  | offset :: frames => { self with frames, offset }
end StackAllocator

structure Ctx where
  /- A mapping from variables in K2 to what register they're stored in in the K1 program -/
  regEnv : List (K2.Var × Reg)
  /- A mapping from variables in K2 to their physical location in SBUF/PSUM -/
  tileEnv : List (K2.Var × (SramMemory × Nat × Nat))
  /- Allocator for sbuf tiles -/
  sbufAllocator : StackAllocator
  /- Aloocator for psum tiles -/
  psumAllocator : StackAllocator
  /- Allocator for registers -/
  regAllocator : StackAllocator
  gensymEnv : GensymEnv := default
deriving Inhabited, Repr

instance : ToString Ctx where
  toString _ :=
    /- TODO: -/
    s!"Ctx (...)"

/- The compilation monad for K1 -/
abbrev Compile T := EStateM String Ctx T

/- Push a new frame onto the stack for the register allocator -/
def pushRegFrame : Compile Unit := do
  let ctx ← get
  let regAllocator := ctx.regAllocator.pushFrame
  modify fun ctx => { ctx with regAllocator }
/- Pop the current frame from the stack for the register allocator -/
def popRegFrame : Compile Unit := do
  let ctx ← get
  let regAllocator := ctx.regAllocator.popFrame
  modify fun ctx => { ctx with regAllocator }

/- Push a new frame onto the stack for the sbuf and psum allocators -/
def pushFrame : Compile Unit := do
  let ctx ← get
  let sbufAllocator := ctx.sbufAllocator.pushFrame
  let psumAllocator := ctx.psumAllocator.pushFrame
  modify fun ctx => { ctx with sbufAllocator, psumAllocator}
  pushRegFrame

/- Pop the current frame from the stack for the sbuf and psum allocators -/
def popFrame : Compile Unit := do
  let ctx ← get
  let sbufAllocator := ctx.sbufAllocator.popFrame
  let psumAllocator := ctx.psumAllocator.popFrame
  modify fun ctx => { ctx with sbufAllocator, psumAllocator}
  popRegFrame

/- Run the function `f` with a new frame, which will be popped after `f` returns. -/
def withFrame (f : Compile T) : Compile T := do
  pushFrame
  let result ← f
  popFrame
  return result

/- Run the function `f` with a new register frame, which will be popped after `f` returns. -/
def withRegFrame (f : Compile T) : Compile T := do
  pushRegFrame
  let result ← f
  popRegFrame
  return result

/- Allocate a tile in sbuf. -/
def sbufAlloc (dtype : Core.Dtype) (size : Nat) : Compile (Nat × Nat) := do
  let ctx ← get
  let (addr, sbufAllocator) := ctx.sbufAllocator.alloc dtype size
  modify fun ctx => { ctx with sbufAllocator }
  return (0, addr)

/- Allocate a tile in psum. -/
def psumAlloc (dtype : Core.Dtype) (size : Nat) : Compile (Nat × Nat) := do
  let ctx ← get
  let (addr, psumAllocator) := ctx.psumAllocator.alloc dtype size
  modify fun ctx => { ctx with psumAllocator }
  return (0, addr)

/- Get a new register that is unused. -/
def regAlloc : Compile Reg := do
  let ctx ← get
  let (regNum, regAllocator) := ctx.regAllocator.alloc .uint8 1
  modify fun ctx => { ctx with regAllocator }
  return ⟨ regNum ⟩

/- Associate a variable in K2 with a register in K1. -/
def associateReg (v : K2.Var) (reg : Reg) : Compile Unit :=
  modify fun ctx => { ctx with regEnv := (v, reg) :: ctx.regEnv }

/- Find what register a variable in K2 is associated with. -/
def lookupReg (v : K2.Var) : Compile Reg := do
  match (← get).regEnv.lookup v with
  | some reg => pure reg
  | none => throw s!"KLR.K.K1.lookup: Variable {v} not found in context"

/- Find which physical location a tile from the K2 program is allocated at. -/
def lookupTile (v : K2.Var) : Compile (SramMemory × Nat × Nat) := do
  match (← get).tileEnv.lookup v with
  | some location => pure location
  | none => throw s!"KLR.K.K1.lookupTile: Variable {v} not found in context"

/- Generate a fresh symbol -/
def gensym (suggestion : String) : Compile String := do
  let (name, env) := (← get).gensymEnv.gensym suggestion
  modify fun ctx => { ctx with gensymEnv := env }
  return name

mutual
  def compileExprWithReg (destReg : Reg) (expr : K2.ScalarK2) : Compile (ScalarK1 × List StatementK1) := do
    let (imm, statements) ← compileExpr expr
    match imm with
    | .float f =>
      pure $ (.float f, statements)
    | .int n =>
      pure $ (.int n, statements)
    | .reg reg =>
      let front := statements.take (statements.length - 1)
      match statements.getLast? with
      | .some (.move _ source) =>
        pure $ (.reg destReg, front ++ [.move destReg source])
      | .some _ =>
        panic! s!"compileExprWithReg: Expected move statement, got {repr statements}"
      | .none =>
        pure $ (.reg reg, [])
    | .address memory parOffset freeOffset =>
      pure $ (.address memory parOffset freeOffset, statements)

  def compileExpr (expr : K2.ScalarK2) : Compile (ScalarK1 × List StatementK1) := do
    match expr with
    | .float f => pure $ (.float f, [])
    | .int n => pure $ (.int n, [])
    | .var var => do
      pure $ (.reg (← lookupReg var), [])
    | .expr op a b =>
      let destReg ← regAlloc
      let statements ← withFrame ((fun _ => do
        let aReg ← regAlloc
        let bReg ← regAlloc
        let (aImm, aStatements) ← withRegFrame (compileExprWithReg aReg a)
        let (bImm, bStatements) ← withRegFrame (compileExprWithReg bReg b)
        let body := match op with
          | .add =>  (RegOp.add  aImm bImm)
          | .mult => (RegOp.mult aImm bImm)
        pure $ aStatements ++ bStatements ++ [.move destReg body]
      ) ())
      pure (.reg destReg, statements)
    | .address name => do
      let (memory, parOffset, freeOffset) ← lookupTile name
      pure $ (.address memory parOffset freeOffset, [])
end

/- Allocates space for a tile in its memory region and adds the mapping to the compilation
context. Call `fetchTensor` afterwards to use the allocated location. -/
def allocateTensor (t : K2.TensorK2) : Compile Unit := do
  let (parOffset, freeOffset) ← match t.memory with
    | .sbuf => sbufAlloc t.dtype (Core.accessSize t.freePattern)
    | .psum => psumAlloc t.dtype (Core.accessSize t.freePattern)
    | .unknown => panic s!"allocateTensor: Unknown memory type for tensor {t.name}"
  modify fun ctx => { ctx with tileEnv := (t.name, (t.memory, parOffset, freeOffset)) :: ctx.tileEnv }

/- Convert an unallocate K2 tensor to a K1 tensor at the proper location, assuming that
`allocateTensor` has been called on it previously. -/
def fetchTensor (t : K2.TensorK2) : Compile TensorK1 := do
  let (memory, parOffset, freeOffset) ← lookupTile t.name
  pure {
    name := t.name,
    dtype := t.dtype,
    memory,
    parOffset := parOffset,
    parNum := t.parNum,
    freeOffset,
    freePattern := t.freePattern
  }

/- Converts an HBM location (offset into a HBM tensor) in K2 to a K1 HBM location by compiling
the offset expression into a series of register operations. -/
def compileHbmLocation (t : K2.HbmLocationK2) : Compile (HbmLocationK1 × List StatementK1) := do
  let (reg, statements) ← compileExpr t.offset
  pure ({
    name := t.name,
    offset := reg,
    pattern := t.pattern,
  }, statements)

/- Compiles a K2 operator into a list of K1 statements. -/
def compileOperator (op : K2.OperatorK2) : Compile (List StatementK1) := do
  match op with
  | .activate ⟨dst, src, accumCmd, op, scale, bias, imm⟩ =>
    let (scale, scaleStatements) ← compileExpr scale
    let (bias, biasStatements) ← compileExpr bias
    let (imm, immStatements) ← compileExpr imm
    pure $
      scaleStatements ++ biasStatements ++ immStatements ++
      [.op (.activate ⟨← fetchTensor dst, ← fetchTensor src, accumCmd, op, scale, bias, imm⟩)]
  | .tensorTensor ⟨dst, a, b, op⟩ =>
    pure $ [.op (.tensorTensor ⟨← fetchTensor dst, ← fetchTensor a, ← fetchTensor b, op⟩)]
  | .tensorScalar ⟨dst, src, imm0, op0, imm1, op1, reverse⟩ =>
    let (imm0, imm0Statements) ← compileExpr imm0
    let (imm1, imm1Statements) ← compileExpr imm1
    pure $
      imm0Statements ++ imm1Statements ++
      [.op (.tensorScalar ⟨← fetchTensor dst, ← fetchTensor src, imm0, op0, imm1, op1, reverse⟩)]
  | .tensorReduce ⟨dst, src, op, opDim, negated⟩ =>
    pure $ [.op (.tensorReduce ⟨← fetchTensor dst, ← fetchTensor src, op, opDim, negated⟩)]
  | .copy ⟨dst, src, opDim⟩ =>
    pure $ [.op (.copy ⟨← fetchTensor dst, ← fetchTensor src, opDim⟩)]
  | .loadStationary ⟨stationary, isTranspose⟩ =>
    pure $ [.op (.loadStationary ⟨← fetchTensor stationary, isTranspose⟩)]
  | .matMul ⟨dst, a, isTranspose⟩ =>
    pure $ [.op (.matMul ⟨← fetchTensor dst, ← fetchTensor a, isTranspose⟩)]
  | .memSet ⟨dst, value, size⟩ =>
    let (value, valueStatements) ← compileExpr value
    pure $ valueStatements ++ [.op (.memSet ⟨← fetchTensor dst, value, size⟩)]
  | _ => panic s!"compileStatement: Unsupported operator {repr op}"

/- Compiles a K2 statement into a list of K1 statements. -/
def compileStatement (s : K2.StatementK2) : Compile (List StatementK1) := do
  match s with
  | .comment s => pure [.comment s]
  | .op op => compileOperator op
  | .loop var start stop step body =>
    withFrame $ (fun _ => do
      let reg ← regAlloc
      associateReg var reg
      let body ← body.flatMapM compileStatement
      pure $ [.loop reg start stop step body]
    ) ()
  | .ifzero var consequent alternate =>
    let consequentStatements ← withFrame $ consequent.flatMapM compileStatement
    let alternateStatements ← withFrame $ alternate.flatMapM compileStatement
    pure $ [.ifzero (← lookupReg var) consequentStatements alternateStatements]
  | .load dst src =>
    let dst ← fetchTensor dst
    let (src, srcStatements) ← compileHbmLocation src
    pure $ srcStatements ++ [.load dst src]
  | .store dst src =>
    let (dst, dstStatements) ← compileHbmLocation dst
    let src ← fetchTensor src
    pure $ dstStatements ++ [.store dst src]
  | .dramToDram dst src =>
    let (dst, dstStatements) ← compileHbmLocation dst
    let (src, srcStatements) ← compileHbmLocation src
    pure $ dstStatements ++ srcStatements ++ [.dramToDram dst src]
  | .assign var expr =>
    /- TODO: how to handle this?-/
    let (imm, statements) ← compileExpr expr
    match imm with
      | .reg r =>
        associateReg var r
        pure statements
      | _ =>
        let reg ← regAlloc
        associateReg var reg
        pure $ statements ++ [.move reg (.imm imm)]

/- Allocates space for all tensors in a K2 statement -/
partial def allocateTensors (statement : K2.StatementK2) : Compile Unit := do
  match statement with
  | .comment .. => pure ()
  | .op .. => pure ()
  | .loop _ _ _ _ body =>
    withFrame $ body.forM allocateTensors
  | .ifzero _ consequent alternate =>
    withFrame $ consequent.forM allocateTensors
    withFrame $ alternate.forM allocateTensors
  | .load dst _ =>
    allocateTensor dst
  | .store _ src =>
    allocateTensor src
  | .dramToDram .. => pure ()
  | .assign .. => pure ()

/- Compiles a K2 program into a K1 program. -/
def compileProgram (f : K2.ProgramK2) : Compile ProgramK1 := do
  f.statements.forM allocateTensors
  let statements ← f.statements.flatMapM compileStatement
  pure {
    name := f.name,
    tensors := f.tensors
    inputs := f.inputs,
    outputs := f.outputs,
    statements
  }

def compile (f : K2.ProgramK2) : (Except String ProgramK1) × Ctx :=
  let compiled := compileProgram f
  match compiled.run default with
  | .ok ops s => (.ok ops, s)
  | .error err s => (throw err, s)
