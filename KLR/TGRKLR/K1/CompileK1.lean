import Lean
import TensorLib.Tensor
import Util.Gensym
import KLR.TGRKLR.Operators
import KLR.TGRKLR.K2.AST
import KLR.TGRKLR.K1.AST

namespace KLR.TGRKLR.K1

open KLR.TGR(TensorTy)

structure BumpAllocator where
  frames : List Nat
  offset : Nat
deriving Inhabited, Repr

namespace BumpAllocator
def alloc (self : BumpAllocator) (_dtype : Core.Dtype) (size : Nat) : (Nat × BumpAllocator) :=
  -- TODO: take into account dtype
  let location := self.offset
  let self := { self with offset := self.offset + size }
  (location, self)
def pushFrame (self : BumpAllocator) : BumpAllocator :=
  { self with frames := self.offset :: self.frames }
def popFrame (self : BumpAllocator) : BumpAllocator :=
  match self.frames with
  | [] => panic "BumpAllocator.popFrame: No frames to pop"
  | offset :: frames => { self with frames, offset }
end BumpAllocator

structure Ctx where
  regEnv : List (K2.Var × Reg)
  tileEnv : List (K2.Var × (Core.SramMemory × Core.ParQuadrant × Nat))
  sbufAllocator : BumpAllocator
  psumAllocator : BumpAllocator
  regAllocator : BumpAllocator
  gensymEnv : GensymEnv := default
deriving Inhabited, Repr

instance : ToString Ctx where
  toString _ :=
    /- TODO: -/
    s!"Ctx (...)"

abbrev Compile T := EStateM String Ctx T

def pushRegFrame : Compile Unit := do
  let ctx ← get
  let regAllocator := ctx.regAllocator.pushFrame
  modify fun ctx => { ctx with regAllocator }
def popRegFrame : Compile Unit := do
  let ctx ← get
  let regAllocator := ctx.regAllocator.popFrame
  modify fun ctx => { ctx with regAllocator }

def pushFrame : Compile Unit := do
  let ctx ← get
  let sbufAllocator := ctx.sbufAllocator.pushFrame
  let psumAllocator := ctx.psumAllocator.pushFrame
  modify fun ctx => { ctx with sbufAllocator, psumAllocator}
  pushRegFrame

def popFrame : Compile Unit := do
  let ctx ← get
  let sbufAllocator := ctx.sbufAllocator.popFrame
  let psumAllocator := ctx.psumAllocator.popFrame
  modify fun ctx => { ctx with sbufAllocator, psumAllocator}
  popRegFrame

def withFrame (f : Compile T) : Compile T := do
  pushFrame
  let result ← f
  popFrame
  return result

def withRegFrame (f : Compile T) : Compile T := do
  pushRegFrame
  let result ← f
  popRegFrame
  return result

def sbufAlloc (dtype : Core.Dtype) (size : Nat) : Compile (Core.ParQuadrant × Nat) := do
  let ctx ← get
  let (addr, sbufAllocator) := ctx.sbufAllocator.alloc dtype size
  modify fun ctx => { ctx with sbufAllocator }
  return (.par0, addr)

def psumAlloc (dtype : Core.Dtype) (size : Nat) : Compile (Core.ParQuadrant × Nat) := do
  let ctx ← get
  let (addr, psumAllocator) := ctx.psumAllocator.alloc dtype size
  modify fun ctx => { ctx with psumAllocator }
  return (.par0, addr)

def regAlloc : Compile Reg := do
  let ctx ← get
  let (regNum, regAllocator) := ctx.regAllocator.alloc .uint8 1
  modify fun ctx => { ctx with regAllocator }
  return ⟨ regNum ⟩

def associateReg (v : K2.Var) (reg : Reg) : Compile Unit :=
  modify fun ctx => { ctx with regEnv := (v, reg) :: ctx.regEnv }

def lookupReg (v : K2.Var) : Compile Reg := do
  match (← get).regEnv.lookup v with
  | some reg => pure reg
  | none => throw s!"KLR.TGRKLR.K1.lookup: Variable {v} not found in context"

def lookupTile (v : K2.Var) : Compile (Core.SramMemory × Core.ParQuadrant × Nat) := do
  match (← get).tileEnv.lookup v with
  | some location => pure location
  | none => throw s!"KLR.TGRKLR.K1.lookupTile: Variable {v} not found in context"

def gensym (suggestion : String) : Compile String := do
  let (name, env) := (← get).gensymEnv.gensym suggestion
  modify fun ctx => { ctx with gensymEnv := env }
  return name


--def compileExprToReg (destReg : Reg) (expr : K2.ScalarK2) : Compile (List StatementK1) := do
--  match expr with
--  | .float f =>
--    pure $ [.move destReg (.imm (.float f))]
--  | .int n =>
--    pure $ [.move destReg (.imm (.int n))]
--  | .var var => do
--    let (memory, parQuadrant, freeOffset) ← lookupTile var
--    pure $ [.move destReg (.imm (.address memory parQuadrant freeOffset))]
--  | .expr op a b =>
--    let statements ← withFrame ((fun _ => do
--      let aReg ← regAlloc
--      let bReg ← regAlloc
--      let aStatements ← withRegFrame (compileExprToReg aReg a)
--      let bStatements ← withRegFrame (compileExprToReg bReg b)
--      let statement := match op with
--        | .add =>  (RegOp.add aReg bReg)
--        | .mult => (RegOp.mult aReg bReg)
--      pure $ aStatements ++ bStatements ++ [.move destReg statement]
--    ) ())
--    pure statements
--  | .address name => do
--    let (memory, parQuadrant, freeOffset) ← lookupTile name
--    pure $ [.move destReg (.imm (.address memory parQuadrant freeOffset))]

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
    let (memory, parQuadrant, freeOffset) ← lookupTile name
    pure $ (.address memory parQuadrant freeOffset, [])
end

def allocateTensor (t : K2.TensorK2) : Compile Unit := do
  let (parQuadrant, freeOffset) ← match t.memory with
    | .sbuf => sbufAlloc t.dtype (Core.accessSize t.freePattern)
    | .psum => psumAlloc t.dtype (Core.accessSize t.freePattern)
  modify fun ctx => { ctx with tileEnv := (t.name, (t.memory, parQuadrant, freeOffset)) :: ctx.tileEnv }

def fetchTensor (t : K2.TensorK2) : Compile TensorK1 := do
  let (memory, parQuadrant, freeOffset) ← lookupTile t.name
  pure {
    name := t.name,
    dtype := t.dtype,
    memory,
    parQuadrant := parQuadrant,
    parDim := t.parDim,
    freeOffset,
    freePattern := t.freePattern
  }

def compileHbmLocation (t : K2.HbmLocationK2) : Compile (HbmLocationK1 × List StatementK1) := do
  let (reg, statements) ← compileExpr t.offset
  pure ({
    name := t.name,
    offset := reg,
    pattern := t.pattern,
  }, statements)

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
