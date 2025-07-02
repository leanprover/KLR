/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.Util
import SHerLOC
import TensorLib.Shape
import TensorLib.Slice
import KLR.HLR.AST

open TensorLib (Shape Dtype)

namespace KLR.HLR

-- Context for the compilation process, to be stored in a state monad.
structure Ctx where
  -- the program being compiled
  program : Program
  -- the log of messages generated during compilation (for debugging)
  log : List String
deriving Inhabited, Repr

namespace Ctx
def empty : Ctx := .mk (.mk []) []
end Ctx

-- Compilation requires tracking state and also potentially returning errors.
abbrev Compile T := EStateM String Ctx T

-- Emit a message to the compilation log.
def log (msg : String) : Compile Unit :=
  modify (fun ctx => { ctx with log := ctx.log ++ [msg]})

-- Add a function to the program being compiled.
def addFunction (func : Function) : Compile Unit := do
  modify (fun ctx =>
    { ctx with program := { ctx.program with functions := ctx.program.functions ++ [func] } })

-- Permute `l` according to the indices in `permutation`.
def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun (dim : Nat) => l[dim]?

-- Parse a StableHLO tensor type from the function signature at index `n`.
def parseTensorType (l : List StableHLO.Parsing.ValueType) (n : Nat): Compile TensorTy :=
  match l[n]? with
  | .some (.tensorType t) => pure (Coe.coe t)
  | .some t => .error s!"Element {n} of type list must have tensor type, but got {repr t}."
  | _ => .error s!"Type list must have at least {n + 1} values, but got only {l.length}."

-- Parse a StableHLO tensor type from a list of types, expecting the list to have exactly one element.
def parseSingleTensorType (l : List StableHLO.Parsing.ValueType) : Compile TensorTy :=
  match l with
  | [.tensorType t] => pure (Coe.coe t)
  | t => .error s!"Expected type list to have a single tensor type, but got {repr t}."

-- Parse an array from a StableHLO literal.
def parseArray (c : StableHLO.Parsing.Literal) : Compile (List Nat) :=
  match c with
  | .array (.array64 arr) => return arr.map (fun (.mk _sign n) => n)
  | .array (.array1 _) => .error "array1 unimplemented."
  | _ => .error "Expected an array of integers."

-- Parse a Nat from a StableHLO float literal.
-- We need this because integers are often represented as floats in StableHLO.
def parseNatFromFloat (c : StableHLO.Parsing.Literal) : Compile Nat :=
  match c with
  | .element (.floatLiteral (.decimal {integerPart, fractionalPart, scientificPart})) =>
    match (fractionalPart.decimal == 0, scientificPart.decimal == 0, integerPart.sign) with
      | (true, true, .plus) => pure integerPart.decimal
      | (false, _, _) | (_, false, _) =>
        .error s!"Expected a non-negative integer, but got a float literal with fractional or scientific part: {repr c}."
      | (_, _, .minus) =>
        .error s!"Expected a non-negative integer, but got a float literal with negative sign: {repr c}."
  | .element (.floatLiteral l) => .error s!"Got unsupported float literal {repr l}."
  | l => .error s!"Expected a float literal but got {repr l}."

-- Find an attribute by name in a list of attributes
def lookupAttribute  (attrs : List StableHLO.Parsing.Attribute) (name : String) : Compile StableHLO.Parsing.Constant :=
  match attrs.find? (fun (.mk id _) => id == name) with
  | some ⟨ _, attr ⟩ => pure attr
  | none => .error s!"Attribute '{name}' not found."

-- Find an attribute by name in a list of attributes, returning only the associated literal, not its type
def lookupAttributeValue (attrs : List StableHLO.Parsing.Attribute) (name : String) : Compile StableHLO.Parsing.Literal :=
  lookupAttribute attrs name |>.map (fun ⟨ lit, _ ⟩ => lit)

-- Get the value of a field in a StableHLO record, expecting it to be a list of integers.
def lookupNatsInFields (fields : List StableHLO.Parsing.StableHLORecordField) (name : String) : Compile (List Nat) :=
  match fields.find? (fun (.mk n _) => n == name) with
  | some (.mk _ (.many ns)) => pure ns
  | some v => .error s!"Field '{name}' must be a list of integers, but got {repr v}."
  | none => pure []

-- Get the value of a field in a StableHLO record, expecting it to be a single integer.
def lookupNatInFields (fields : List StableHLO.Parsing.StableHLORecordField) (name : String) : Compile Nat :=
  match fields.find? (fun (.mk n _) => n == name) with
  | some (.mk _ (.one n)) => pure n
  | some v => .error s!"Field '{name}' must be a single integer, but got {repr v}."
  | none => .error s!"Field '{name}' not found in record list {repr fields}."

-- extract the arguments to the `dotGeneral` operation from a record in the list of attributes
def extractDotDimensionNumbers (attrs : List StableHLO.Parsing.Attribute) : Compile (List Nat × List Nat × List Nat × List Nat) := do
  let dotAttr ← lookupAttributeValue attrs "dot_dimension_numbers"
  match dotAttr with
  | .stableHLORecord fields =>
    let lhs_batching_dims ← lookupNatsInFields fields "lhs_batching_dimensions"
    let lhs_contracting_dims ← lookupNatsInFields fields "lhs_contracting_dimensions"
    let rhs_batching_dims ← lookupNatsInFields fields "rhs_batching_dimensions"
    let rhs_contracting_dims ← lookupNatsInFields fields "rhs_contracting_dimensions"
    pure (lhs_batching_dims, lhs_contracting_dims, rhs_batching_dims, rhs_contracting_dims)
  | _ => .error "Attribute 'dot_dimension_numbers' must be a stableHLORecord."

-- extract the arguments to the `gather` operation from a record in the list of attributes
def extractDimensionNumbers (attrs : List StableHLO.Parsing.Attribute) : Compile (List Nat × List Nat × List Nat × Nat) := do
  let attr ← lookupAttributeValue attrs "dimension_numbers"
  match attr with
  | .stableHLORecord fields =>
    let offset_dims ← lookupNatsInFields fields "offset_dims"
    let collapsed_slice_dims ← lookupNatsInFields fields "collapsed_slice_dims"
    let start_index_map ← lookupNatsInFields fields "start_index_map"
    let index_vector_dim ← lookupNatInFields fields "index_vector_dim"
    pure (offset_dims, collapsed_slice_dims, start_index_map, index_vector_dim)
  | _ => .error "Attribute 'dimension_numbers' must be a stableHLORecord."

-- The StableHLO `reduce` operation always calls an arbitrary reduction function.
-- However, in HLR we only support a few specific reduction operations (mostly
-- arithmetic and logical binary operators). Since many StableHLO programs only
-- use these basic reduction operations, we can recognize when the StableHLO function
-- called by a `reduce` operation is one of these basic operations, and convert it
-- to the corresponding HLR BinaryOp.
-- If this process is unsuccessful, it means that the input `reduce` function is more
-- complicated and can't be supported by the current HLR design.
def reduceFunctionToReduceOp (f : StableHLO.Parsing.InputFunc) : Compile (BinaryOp) := do
  match f with
  | .mk _ [.stablehlo .maximum .., .return ..] => pure .max
  | .mk _ [.stablehlo .add .., .return ..] => pure .add
  | .mk _ [.stablehlo .and .., .return ..] => pure .and
  | .mk _ [.stablehlo op .., .return ..] => .error s!"Unimplemented reduction function {repr op}."
  | op =>
    .error ("Unable to recognize `reduce` function as simple binary operator. Compiling" ++
    "this program likely requires adding support for arbitrary function calling in `reduce`"
    ++ s!"Function: {repr op}")

-- Compile a StableHLO operation into a list of HLR statements.
--
-- Note: this function annotates each statement with the type of its output,
-- but this type is merely passed through from the HLO program, not computed anew.
-- This means it's possible that if there's a mistake in the shape calculation
-- in the HLO program, the HLR statements will also have incorrect shapes.
-- Eventually, we'll want a function that can shape-check an HLR program.
def compileOp : StableHLO.Parsing.Operation → Compile (List Statement)
  | .stablehlo opCode inputValues inputFunctions inputAttributes outputs signature => do
    -- Reuse the variable names and shapes from the StableHLO program
    let output ← match outputs with
    | [output] => pure output
    | _ => .error "Operator signature must have a single output."
    let outputTy ← parseSingleTensorType signature.range
    -- helper function to emit HLR for element-wise unary ops
    let makeUnOp := fun (op : UnaryOp) => do
      log s!"Compiling unary op {op}"
      let a := inputValues[0]!
      pure [.assign output (.unaryOp op a) outputTy]
    -- helper function to emit HLR for element-wise binary ops
    let makeBinOp := fun (op : BinaryOp) => do
      log s!"Compiling binary op {op}"
      let a := inputValues[0]!
      let b := inputValues[1]!
      pure [.assign output (.binaryOp op a b) outputTy]
    match opCode with
    -- element-wise unary operators
    | .sqrt => makeUnOp .sqrt
    | .negate => makeUnOp .neg
    | .exponential => makeUnOp .exp
    | .convert => makeUnOp (UnaryOp.convert outputTy.dtype)
    -- element-wise binary operators
    | .compare => makeBinOp .cmp
    | .multiply => makeBinOp .mul
    | .add => makeBinOp .add
    | .and => makeBinOp .and
    | .maximum => makeBinOp .max
    | .subtract =>  makeBinOp .sub
    | .divide =>  makeBinOp .div
    -- tensor nullary operators
    | .constant =>  do
      log "Compiling constant operation"
      let valueAttr ← lookupAttributeValue inputAttributes "value"
      match valueAttr with
      | (.tensor (.denseElements [(.floatLiteral f)])) =>
        pure [.assign output (.full f outputTy.shape) outputTy]
      | (.tensor lit) =>
        pure [.assign output (.const lit outputTy.shape outputTy.dtype) outputTy]
      | _ => .error "Constant operation requires a 'value' attribute with tensor literal."
    -- tensor unary operators
    | .reshape => do
      log "reshape"
      let input := inputValues[0]!
      pure [.assign output (.reshape input outputTy.shape) outputTy]
    | .gather =>
      log "Compiling gather operation"
      let (offsetDims, collapsedSliceDims, startIndexMap, indexVectorDim) ←
        extractDimensionNumbers inputAttributes
      let input := inputValues[0]!
      let indices := inputValues[1]!
      pure [.assign output (.gather input indices offsetDims collapsedSliceDims startIndexMap indexVectorDim) outputTy]
    | .slice =>
      log "Compiling slice operation"
      let input := inputValues[0]!
      let start ← (← lookupAttributeValue inputAttributes "start_indices") |> parseArray
      let limit ← (← lookupAttributeValue inputAttributes "limit_indices") |> parseArray
      let stride ← (← lookupAttributeValue inputAttributes "strides") |> parseArray
      pure [.assign output (.slice input start limit stride) outputTy]
    | .reduce =>
      log "Compiling reduce operation"
      let op ← reduceFunctionToReduceOp inputFunctions[0]!
      let dims ← (← lookupAttributeValue inputAttributes "dimensions") |> parseArray
      pure [.assign output (.reductionOp op inputValues[0]! inputValues[1]! dims) outputTy] -- TODO: init value
    | .broadcastInDim => do
      log "Compiling broadcastInDim operation"
      let input := inputValues[0]!
      pure [.assign output (.broadcast input outputTy.shape) outputTy]
    | .transpose => do
      log "Compiling transpose operation"
      let input := inputValues[0]!
      let dims ← (← lookupAttributeValue inputAttributes "permutation") |> parseArray
      pure  [.assign output (.transpose input dims) outputTy]
    -- tensor binary operators
    | .dotGeneral => do
      -- The semantics of the `dotGeneral` operation are complex, see the
      -- specification for details. The variables here are named similar to the
      -- variables in the spec to aid comprehension.
      -- https://github.com/openxla/stablehlo/blob/6f7b4ab8f96dc65cf3c8e9824836117d2934cc45/docs/spec.md?#dot_general
      log "Compiling dotGeneral operation"
      -- Gather metadata from the inputs
      let (lhsBatchingDims, lhsContractingDims, rhsBatchingDims, rhsContractingDims) ←
        extractDotDimensionNumbers inputAttributes
      let lhs := inputValues[0]!
      let rhs := inputValues[1]!
      let lhsType ← parseTensorType signature.domain 0
      let rhsType ← parseTensorType signature.domain 1
      let dtype := lhsType.dtype
      let lhsShape := lhsType.shape
      let rhsShape := rhsType.shape
      let lhsDims :=  List.range (TensorLib.Shape.ndim lhsShape)
      let rhsDims :=  List.range (TensorLib.Shape.ndim rhsShape)
      -- Calculate shapes of intermediate tensors and output
      let lhsResultDims := lhsDims.filter (fun i => !lhsBatchingDims.contains i && !lhsContractingDims.contains i)
      let rhsResultDims := rhsDims.filter (fun i => !rhsBatchingDims.contains i && !rhsContractingDims.contains i)
      let lhsTransposePerm := lhsBatchingDims ++ lhsResultDims ++ lhsContractingDims
      let rhsTransposePerm := rhsBatchingDims ++ rhsResultDims ++ rhsContractingDims
      let lhsTransposedShape := permute lhsShape.val lhsTransposePerm |>.get!
      let rhsTransposedShape := permute rhsShape.val rhsTransposePerm |>.get!
      let batchShape := lhsTransposedShape.take lhsBatchingDims.length
      let lhsResultShape := lhsTransposedShape.drop lhsBatchingDims.length |>.take lhsResultDims.length
      let rhsResultShape := rhsTransposedShape.drop rhsBatchingDims.length |>.take rhsResultDims.length
      let contractingShape := lhsTransposedShape.drop (lhsBatchingDims.length + lhsResultDims.length) |>
        List.take (lhsTransposedShape.length - (lhsBatchingDims.length + lhsResultDims.length))
      let batchSize := if batchShape.isEmpty then 1 else batchShape.foldl (fun acc d => acc * d) 1
      let resultShape := batchShape ++ lhsResultShape ++ rhsResultShape
      let lhsResultSize := if lhsResultShape.isEmpty then 1 else lhsResultShape.foldl (fun acc d => acc * d) (1 : Nat)
      let rhsResultSize := if rhsResultShape.isEmpty then 1 else rhsResultShape.foldl (fun acc d => acc * d) (1 : Nat)
      let contractingSize := if contractingShape.isEmpty then 1 else contractingShape.foldl (fun acc d => acc * d) 1
      -- Create fresh variable names for intermediate results
      let lhsTransposedName := lhs ++ "_transposed"
      let rhsTransposedName := rhs ++ "_transposed"
      let lhsReshapedName := lhs ++ "_reshaped"
      let lhsReshapedShape := [batchSize, lhsResultSize, contractingSize]
      let lhsReshapedTy := TensorTy.mk (.mk lhsReshapedShape) dtype
      let rhsReshapedName := rhs ++ "_reshaped"
      let rhsReshapedShape := [batchSize, rhsResultSize, contractingSize]
      let rhsReshapedTy := TensorTy.mk (.mk rhsReshapedShape) dtype
      let resultReshapedName := output ++ "_reshaped"
      let resultReshapedShape := [batchSize, lhsResultSize, rhsResultSize]
      let resultReshapedType := TensorTy.mk (.mk resultReshapedShape) dtype
      -- Emit the HLR statements for the dotGeneral operation
      pure ([
        .comment "Dot General Operation",
        .assign lhsTransposedName (.transpose lhs lhsTransposePerm) (.mk (.mk lhsTransposedShape) dtype),
        .assign rhsTransposedName (.transpose rhs rhsTransposePerm) (.mk (.mk rhsTransposedShape) dtype),
        .assign lhsReshapedName (.reshape lhsTransposedName lhsReshapedTy.shape) lhsReshapedTy,
        .assign rhsReshapedName (.reshape rhsTransposedName rhsReshapedTy.shape) rhsReshapedTy,
        .assign resultReshapedName (.batchMatmul lhsReshapedName rhsReshapedName) resultReshapedType,
        .assign output (.reshape resultReshapedName (.mk resultShape)) outputTy,
      ])
    | .concatenate =>
      log "Compiling concatenate operation"
      let tensors := inputValues
      let dim ← (← lookupAttributeValue inputAttributes "dimension") |> parseNatFromFloat
      pure [.assign output (.concat tensors dim) outputTy]
    -- tensor ternary operators
    | .select =>
      log "Compiling select operation"
      let cond := inputValues[0]!
      let a := inputValues[1]!
      let b := inputValues[2]!
      pure [.assign output (.select cond a b) outputTy]
    | _ => .error s!"Unsupported HLO operation: {repr opCode}"
  | .return ops _ => do
    log "Compiling return operation"
    pure [Statement.ret ops]
  | .call callee inputValues outputs signature => do
    log "Compiling call operation"
    let output ← match outputs with
    | [output] => pure output
    | _ => .error "Call operator signature must have a single output."
    pure [
      Statement.assign
        output
        (.call callee inputValues)
        (← parseSingleTensorType signature.range)]

  | s => .error s!"Unsupported operation type {repr s}"

def compileFunc (f : StableHLO.Parsing.Function) : Compile Unit := do
  let .mk args body := f.funcBody
  let inputs ← args.mapM (fun (.mk name v) => do
    match v with
    | .tensorType t => pure t
    | _ => .error s!"Function input {name} must have tensor type.")
  let outputs ← f.funcType.range.mapM fun x => match x with
    | .tensorType t => pure t
    | _ => .error "Function output must be a tensor type."
  -- Since arguments are referred to by index, emit a statement for each
  -- argument that assigns it to a named variable
  let preamble ← args.mapIdxM (fun i (.mk name v) => do
    match v with
    | .tensorType t =>
      pure (Statement.assign name (.arg i) t)
    | _ => .error s!"Function input {name} must have tensor type.")
  let statements ← body.flatMapM compileOp
  let func := Function.mk f.funcId inputs outputs (preamble ++ statements)
  addFunction func

def compileModule (m : StableHLO.Parsing.Module) : Compile Unit :=
  m.modFuncs.forM compileFunc

def compile (m : List StableHLO.Parsing.Module) : (Except String Unit) × Ctx :=
  let compiled := match m with
    | [m] => compileModule m
    | _  => .error "Only one module is supported for now."
  match compiled.run Ctx.empty with
  | .ok _ s => (.ok (), s)
  | .error err s => (.error err, s)

end KLR.HLR
