import KLR.K.K1.AST
import KLR.K.Operators
import TensorLib.Tensor

namespace KLR.K.K1.Interp

open KLR.TGR(TensorTy)
open Std.Format

inductive Value where
  | none
  | int (n : Int)
  | float (f : Float32)
  | address (memory : SramMemory) (parOffset : Nat) (freeOffset : Nat)
deriving Inhabited, Repr, BEq

structure Partition where
  (data : Vector Value 100)
deriving Repr, Inhabited, BEq

structure Ctx where
  dram : Std.HashMap Var (Array Value)
  sbuf : Vector Partition 128
  psum : Vector Partition 128
  regs : Vector Value 32
  peState : Array (Array Value)
  log : List String
deriving Repr, Inhabited, BEq

abbrev Interp T := EStateM String Ctx T

def log (msg : String) : Interp Unit := do
  dbg_trace msg
  modify fun ctx => { ctx with log := ctx.log ++ [msg] }

instance : ToString Value where
  toString
    | .none => "none"
    | .int n => s!"int({n})"
    | .float f => s!"float({f})"
    | .address memory parOffset freeOffset =>
      s!"address({memory},{parOffset},{freeOffset})"

instance : ToString (Vector Value N) where
  toString v :=
    let values := v.toList.map (fun x => toString x)
    s!"[{String.intercalate ", " values}]"
instance : ToString Partition where
  toString p := s!"Partition({p.data})"

instance : ToString Ctx where
  toString ctx :=
    let dramStr := ctx.dram.toList.map (fun (k, v) => s!"{k} -> {v}") |>.intersperse "\n"
    let sbufStr := (ctx.sbuf.toList.map toString)     |>.intersperse "\n"
    let psumStr := ctx.psum.toList.map toString       |>.intersperse "\n"
    let regsStr := ctx.regs.toList.map toString       |>.intersperse ", "
    let peStateStr := ctx.peState.toList.map toString |>.intersperse "\n"
    let logStr := ctx.log |>.intersperse "\n"
    s!"Dram:\n{dramStr}\n\nSbuf:\n{sbufStr}\n\nPsum:\n{psumStr}\n\nRegs: [{regsStr}]\n\nPE State:\n{peStateStr}\n\nLog:\n{logStr}"

def accessToIndices (pattern : List Core.APPair) : Array Nat :=
  let rec helper (acc : Array Nat) (pattern : List Core.APPair) :=
    match pattern with
    | ⟨step, num⟩ :: rest => Id.run do
      let out := Array.range' 0 num step.toNat
        |>.map (fun i => acc.map (fun x => x + i))
        |>.flatten
      helper out rest
    | [] => acc
  helper #[0] pattern

def dramAccess (src : Var) (offset : Nat) (pattern : List Core.APPair) : Interp (Array Value) := do
  let indices := accessToIndices pattern
  let data := (← get).dram[src]!
  if offset + indices.back! > data.size then
    panic! s!"Dram access of {src} at offset {offset} with pattern {repr pattern} exceeds size {data.size}"
  let values := indices.map (fun i => data[i + offset]!)
  if values.any fun x => x == .none then
    panic! s!"Dram access uninitialized value in {src} at offset {offset} with pattern {repr pattern}"
  else
    pure values

def dramWrite
  (dest : Var) (destOffset : Nat) (destPattern : List Core.APPair)
  (sourceData : Array Value) : Interp Unit := do
  let indices := accessToIndices destPattern
  if indices.size != sourceData.size then
    throw s!"Size mismatch in dramWrite: {indices.size} != {sourceData.size}"
  let mut newDram := (← get).dram[dest]!
  for i in List.range indices.size do
    let index := destOffset + indices[i]!
    log s!"Writing to dram[{dest}][{index}] = {sourceData[i]!} (tensor size: {newDram.size})"
    newDram := newDram.set! index (sourceData[i]!)
  modify fun ctx => { ctx with dram := ctx.dram.insert dest newDram }

def sbufWrite (dest : TensorK1) (data : Array Value) : Interp Unit := do
  if data.isEmpty then
    log "sbufWrite: Data is empty"
    throw "sbufWrite: Data cannot be empty"
  let {name, dtype := _dtype, memory, parNum, freePattern, parOffset, freeOffset} := dest
  let accessIndices := accessToIndices freePattern
  let startRow := parOffset
  let mem ← match memory with
    | .sbuf => EStateM.get |>.map fun ctx => ctx.sbuf
    | .psum => EStateM.get |>.map fun ctx => ctx.psum
    | .unknown => panic s!"sbufWrite: Unknown memory type for tensor {name}"
  let mut mem := mem
  if accessIndices.size * parNum != data.size then
    throw s!"Size mismatch in sbufWrite: {accessIndices.size * parNum} != {data.size}"
  let mut i := 0
  for row in [startRow:startRow + parNum] do
    for accessIndex in accessIndices do
      let index := freeOffset + accessIndex
      if index >= 4096 then
        throw s!"Index out of bounds in sbufWrite: {index} >= 4096"
      if i >= data.size then
        throw s!"Data index out of bounds in sbufWrite: {i} >= {data.size}"
      log s!"Writing to sbuf[{row}][{index}] = {data[i]!}"
      mem := mem.set! row ⟨mem[row]!.data.set! index data[i]!⟩
      i := i + 1
  match memory with
  | .sbuf => modify fun ctx => { ctx with sbuf := mem }
  | .psum => modify fun ctx => { ctx with psum := mem }
  | .unknown => panic s!"sbufWrite: Unknown memory type for tensor {name}"

def sbufRead (src : TensorK1) : Interp (Array Value) := do
  let {name, dtype := _dtype, memory, parNum, freePattern, parOffset, freeOffset} := src
  let accessIndices := accessToIndices freePattern
  let startRow := parOffset
  let mem ← match memory with
    | .sbuf => EStateM.get |>.map fun ctx => ctx.sbuf
    | .psum => EStateM.get |>.map fun ctx => ctx.psum
    | .unknown => panic s!"sbufRead: Unknown memory type for tensor {name}"
  let mut values := Array.mkEmpty (accessIndices.size * parNum)
  for row in [startRow:startRow + parNum] do
    for accessIndex in accessIndices do
      let index := freeOffset + accessIndex
      if index >= 4096 then
        throw s!"Index out of bounds in sbufRead: {index} >= 4096"
      log s!"Reading from sbuf[{row}][{index}]"
      let value := mem[row]!.data[index]!
      if value == .none then
        throw s!"Uninitialized value in sbufRead at sbuf[{row}][{index}]"
      values := values.push value
  pure values

def interpScalar (scalar : ScalarK1) : Interp Value := do
  match scalar with
  | .float f => pure (.float f)
  | .int i => pure (.int i)
  | .reg reg => do
    let value := (← get).regs[reg.reg]?
    match value with
    | .none => throw s!"Variable {reg} is not initialized"
    | .some v => pure v
  | .address memory parOffset freeOffset =>
    pure (.address memory parOffset freeOffset)

def interpRegop (expr : RegOp) : Interp Value := do
  match expr with
  | .imm imm => interpScalar imm
  | .add a b => do
    let aVal ← interpScalar a
    let bVal ← interpScalar b
    match aVal, bVal with
    | .float a, .float b => pure (.float (a + b))
    | .int a, .int b => pure (.int (a + b))
    | _, _ => throw s!"Expected float or int values in add, but got {repr aVal} and {repr bVal}"
  | .mult a b => do
    let aVal ← interpScalar a
    let bVal ← interpScalar b
    match aVal, bVal with
    | .float a, .float b => pure (.float (a * b))
    | .int a, .int b => pure (.int (a * b))
    | _, _ => throw s!"Expected float or int values in mult, but got {repr aVal} and {repr bVal}"

def reshape (data : Array Value) (parNum : Nat) (freeDim : Nat) : Interp (Array (Array Value)) := do
  if data.size != parNum * freeDim then
    throw s!"Size mismatch in reshape: {data.size} != {parNum * freeDim}"
  let mut out : Array (Array Value) := Array.emptyWithCapacity parNum
  for i in List.range parNum do
    out := out.push ((data.toSubarray (i * freeDim) ((i + 1) * freeDim)).toArray)
  pure out
def flatten (data : Array (Array Value)) : Interp (Array Value) := do
  let mut out : Array Value := #[]
  for row in data do
    out := out ++ row
  pure out

def aluOpToFun (op : KLR.Core.AluOp) : Interp (Float32 → Float32 → Float32) := do
  let op ← match op with
    | .add => pure (. + .)
    | .subtract => pure (. - .)
    | .mult => pure (. * .)
    | .divide => pure (. / .)
    | .max => pure (fun a b => if a > b then a else b)
    | _ => throw s!"Unsupported tensorTensor operator: {repr op}"

def interpOp (op : OperatorK1) : Interp Unit := do
  match op with
  | .activate ⟨dst, src, _accumCmd, op, _scale, _bias, _imm⟩ =>
    let srcValues ← sbufRead src
    let dstValues ← match op with
    | .copy => pure srcValues
    | .exp => srcValues.mapM fun
        | .float f => pure $ .float f.exp
        | x => throw s!"Expected float in activate, but got {repr x}"
    | _ => throw s!"Unsupported activation op: {repr op}"
    sbufWrite dst dstValues
  | .tensorTensor ⟨dst, a, b, op⟩ =>
    let aValues ← sbufRead a
    let bValues ← sbufRead b
    if aValues.size != bValues.size then
      throw s!"Size mismatch in tensorTensor: {aValues.size} != {bValues.size}"
    let op ← aluOpToFun op
    let dstValues ← aValues.zip bValues |>.mapM (fun (a, b) =>
      match a, b with
      | .float a, .float b =>
        pure $ Value.float (op a b)
      | _, _ => EStateM.throw s!"Expected float values in tensorTensor, but got {repr a} and {repr b}")
    sbufWrite dst dstValues
  | .tensorScalar ⟨dst, src, imm0, op0, _imm1, _op1, _reverse⟩ =>
    let srcValues ← sbufRead src
    let parNum := src.parNum
    let freeDim := accessToIndices src.freePattern |>.size
    let op ← aluOpToFun op0
    let destValues ← match imm0 with
    | .float f => srcValues.mapM fun
        | .float v => pure $ .float (op v f)
        | x => throw s!"Expected float in tensorScalar, but got {repr x}"
    | .reg r =>
      match (← get).regs[r.reg]! with
      | .address memory parOffset freeOffset =>
        let srcValues ← reshape srcValues parNum freeDim
        if parOffset != 0 then
          throw s!"Expected parOffset to be 0 in tensorScalar, but got {parOffset}"
        let vec := { name := "", dtype := src.dtype, memory := memory, parOffset := 0, parNum, freeOffset, freePattern := [⟨1, 1⟩] }
        let vecValues ← sbufRead vec
        log s!"TensorScalar operation with variablevalues: {vecValues} and srcValues: {srcValues}"
        let result ← srcValues.zip vecValues |>.mapM fun (row, scalar) =>
          match scalar with
          | .float scalar => row.mapM (fun value =>
            match value with
            | .float v => pure $ Value.float (op v scalar)
            | x => throw s!"Expected float in tensorScalar, but got {repr x}")
          | x => throw s!"Expected float in tensorScalar, but got {repr x}"
        log s!"TensorScalar operation with variable result: {result}"
        flatten result
      | x => throw s!"Expected address in tensorScalar, but got {repr x}"
    | _ => throw s!"Unsupported immediate type in tensorScalar: {repr imm0}"
    log s!"TensorScalar operation result: {destValues}"
    sbufWrite dst destValues
  | .tensorReduce ⟨dst, src, op, _opDim, _negated⟩ =>
    let parNum := src.parNum
    let freeDim := accessToIndices src.freePattern |>.size
    let srcValues ← sbufRead src
    let tile ← reshape srcValues parNum freeDim
    let op ← aluOpToFun op
    let destValues ← tile.mapM fun row =>
      (row.foldlM (fun acc value =>
        match value with
        | Value.float f => pure $ op acc f
        | _ => throw s!"Expected float value in tensorReduce, but got {repr value}")
      0.0) |> EStateM.map fun result => .float result
    sbufWrite dst destValues
  | .loadStationary ⟨src, _⟩ =>
    let parNum := src.parNum
    let freeDim := accessToIndices src.freePattern |>.size
    let srcValues ← sbufRead src
    let newPeState ← reshape srcValues parNum freeDim
    modify fun ctx => { ctx with peState := newPeState }
  | .matMul ⟨dst, moving, _⟩ =>
    let parNum := moving.parNum
    let freeDim := accessToIndices moving.freePattern |>.size
    let moving ← reshape (← sbufRead moving) parNum freeDim
    let stationary := (← get).peState
    -- simulate np.einsum("bij,bkj->bik", a, b)
    let (iSize, jSize) := (parNum, freeDim)
    let kSize := moving.size
    let mut dest := Array.replicate iSize (Array.replicate kSize (.float 0.0))
    for i in List.range iSize do
      for k in List.range kSize do
        let mut sum := 0.0
        for j in List.range jSize do
          log s!"Multiplying moving[{i}][{j}] with stationary[{j}][{k}] (sum: {sum})"
          sum ← match (moving[i]![j]!, stationary[k]![j]!) with
            | (.float a, .float b) => pure (a * b + sum)
            | _ => throw s!"Expected float values in matMul, but got {repr moving[i]![j]!} and {repr stationary[j]![k]!}"
        dest := dest.set! i (dest[i]!.set! k (.float sum))
    let destValues ← flatten dest
    sbufWrite dst destValues
  | .memSet ⟨dst, value, _⟩ =>
    let parNum := dst.parNum
    let freeDim := accessToIndices dst.freePattern |>.size
    let fillValue ← match value with
      | .float f => pure (.float f)
      | _ => throw s!"Unsupported value type in memSet: {repr value}"
    let destValues := Array.replicate (parNum * freeDim) fillValue
    sbufWrite dst destValues
  | .copy ⟨dst, src, _⟩ =>
    let srcValues ← sbufRead src
    log s!"Copying values from {src} to {dst}: {srcValues}"
    sbufWrite dst srcValues
  | _ => throw s!"Unsupported operator: {repr op}"

partial def interpStatement (statement : StatementK1) : Interp Unit := do
  log s!"--- Statement ---\n{toString statement}"
  match statement with
  | .comment _ => pure ()
  | .op op => interpOp op
  | .loop var start stop step body =>
    let mut counter := start
    while counter < stop do
      modify fun ctx => { ctx with regs := ctx.regs.set! var.reg (.int counter) }
      body.forM interpStatement
      counter := counter + step
  | .ifzero var consequent alternate =>
    if (← get).regs[var.reg]! == (.int 0) then
      consequent.forM interpStatement
    else
      alternate.forM interpStatement
  | .load dst ⟨srcName, srcOffset, srcPattern⟩ =>
    let srcOffset ← match (← interpScalar srcOffset) with
      | .int n => pure n.toNat
      | _ => throw "Expected integer offset for load"
    let sourceValues ← dramAccess srcName srcOffset srcPattern
    sbufWrite dst sourceValues
  | .store ⟨dstName, dstOffset, dstPattern⟩ src =>
    let srcValues ← sbufRead src
    let dstOffset ← match (← interpScalar dstOffset) with
      | .int n => pure n.toNat
      | _ => throw "Expected integer offset for store"
    dramWrite dstName dstOffset dstPattern srcValues
  | .dramToDram ⟨dstName, dstOffset, dstPattern⟩ ⟨srcName, srcOffset, srcPattern⟩ =>
    let srcOffset ← match (← interpScalar srcOffset) with
      | .int n => pure n.toNat
      | _ => throw "Expected integer offset for dramToDram"
    let sourceValues ← dramAccess srcName srcOffset srcPattern
    let dstOffset ← match (← interpScalar dstOffset) with
      | .int n => pure n.toNat
      | _ => throw "Expected integer offset for dramToDram"
    dramWrite dstName dstOffset dstPattern sourceValues
  | .move reg regop =>
    let value ← interpRegop regop
    modify fun ctx => { ctx with regs := ctx.regs.set! reg.reg value }

def interpFunction (f : ProgramK1) : Interp Unit := do
  let _ ← f.statements.mapM (fun stmt => do
    interpStatement stmt)
  pure ()

def interp (klr : ProgramK1) : (Except String Unit) × Ctx := Id.run do
  let mut ctx := default
  for (name, type) in klr.tensors do
    let initialData := Array.replicate type.shape.count (.none)
    ctx := { ctx with dram := ctx.dram.insert name initialData }

  for (name, type) in klr.inputs do
    let hbmTensor ← match type.dtype with
      | .float32 => pure (Array.replicate type.shape.count (Value.float 2.0))
      | _ => panic! s!"Unsupported input dtype: {repr type}"
    ctx := { ctx with dram := ctx.dram.insert name hbmTensor }

  match (interpFunction klr).run ctx with
  | .ok _ s => (.ok (), s)
  | .error err s => (throw err, s)
