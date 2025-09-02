/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Biberstein
-/

import KLR.Core.Operators
import KLR.TGR.AST
import KLR.Util
import SHerLOC
import TensorLib.Shape
import TensorLib.Slice
import TensorLib.Tensor
import TensorLib.Bytes
import TensorLib.ByteArray
import Util.Gensym

open TensorLib (Dtype Shape Tensor)

/- This module compiles a StableHLO program into an TGR program. -/
namespace KLR.TGR.Compile

/- Context for the compilation process, to be stored in a state monad. -/
structure Ctx where
  /- the program being compiled -/
  program : Program
  /- the log of messages generated during compilation (for debugging) -/
  log : List String
  gensymEnv : GensymEnv
deriving Inhabited, Repr

/- Compilation requires tracking state and also potentially returning errors. -/
abbrev Compile T := StM Ctx T

/- Emit a message to the compilation log. -/
def log (msg : String) : Compile Unit :=
  modify (fun ctx => { ctx with log := ctx.log ++ [msg]})

/- Add a function to the program being compiled. -/
def addFunction (func : Function) : Compile Unit := do
  modify (fun ctx =>
    { ctx with program := { ctx.program with functions := ctx.program.functions ++ [func] } })

/-
Generate a fresh variable name based on a given name.
-/
def gensym (suggestion : String) : Compile String := do
  let (name, env) := (← get).gensymEnv.gensym suggestion
  modify fun ctx => { ctx with gensymEnv := env }
  return name

/- Permute `l` according to the indices in `permutation`. -/
def permute {T : Type} (l : List T) (permutation : List Nat) : Option (List T) :=
  permutation.mapM fun dim => l[dim]?

/-
Parses a StableHLO floatliteral to a Float32.

TODO: Probably has all sorts of rounding errors, but dealing with floats in Lean
is so agonizing, and the semantics of this number storage system are so confusing,
that I'm satisfied with this as a first pass for now.

Examples:
The FloatLiteral
  intPart: {.minus, 4}
  fracPart: {.plus, 785980}
  sciPart: {.minus, 1}
Represents the number 4.4785980e-1, which is
  (4 + 0.4785980) * 10 ^ -1

Alternatively, if we have
  intPart: {.minus, 3}
  fracPart: {.plus, 597620}
  sciPart: {.minus, 3}
Then it represents the number -3.597620e-3, which is
  (-3 + 0.597620) * 10 ^ -3
-/
def parseFloat (c : StableHLO.Parsing.FloatLiteral) : Float32 :=
  match c with
  | .decimal {
    integerPart := ⟨ intSign, intDecimal ⟩,
    fractionalPart := ⟨ _, fracDecimal ⟩,
    scientificPart := ⟨ sciSign, sciDecimal ⟩
    } =>
    let exponent := match sciSign with
      | .plus => Int.ofNat sciDecimal
      | .minus => -1 * Int.ofNat sciDecimal
    let sign := match intSign with
      | .plus => 1
      | .minus => (-1 : Float32)
    let mantissa := String.toNat! s!"{intDecimal}{fracDecimal}"
    let fracDigits := ToString.toString fracDecimal |>.length |> Int.ofNat
    let exponent := exponent - fracDigits
    let (exponentSign, exponent) := if exponent >= 0 then
      (false, exponent.natAbs)
    else
      (true, exponent.natAbs)
    sign * OfScientific.ofScientific mantissa exponentSign exponent
  | .hexaDecimal n => UInt32.ofNat n |> Float32.ofBits

#guard parseFloat (.decimal { integerPart := ⟨ .plus,  4 ⟩, fractionalPart := ⟨ .plus, 785980 ⟩, scientificPart := ⟨ .plus,  3 ⟩}) == 4785.980
#guard parseFloat (.decimal { integerPart := ⟨ .minus, 4 ⟩, fractionalPart := ⟨ .plus, 785980 ⟩, scientificPart := ⟨ .minus, 1 ⟩}) == -0.4785980
#guard parseFloat (.decimal { integerPart := ⟨ .minus, 3 ⟩, fractionalPart := ⟨ .plus, 597620 ⟩, scientificPart := ⟨ .minus, 3 ⟩}) == -0.003597620

/-
Parses a hex string (starting with "0x" and preceded by a multipleof 8 hex characters)
into a tensor of int32 values.

Assumes bytes are in big-endian order.
-/
def parseInt32TensorFromHex (s : String) : Compile Tensor := do
  /- Tail recursive helper to convert a list of hex characters to a list of BitVec 32 values. -/
  let rec toBitVec32List (str : List Char) (acc : List (BitVec 32)) : Compile (List (BitVec 32)):= do
    match str with
    | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
      match KLR.Util.Hex.hexCharsToBitVecBE c0 c1 c2 c3 c4 c5 c6 c7 with
      | some v => toBitVec32List rest (v :: acc)
      | none => throw s!"Invalid hex character sequence: {c0}{c1}{c2}{c3}."
    | [] => pure acc.reverse
    | _ => throw s!"Hex string must have a number of characters divisible by 8, but got {str}."

  /- Trim off the leading "0x" and convert the rest to a list of BitVec 32 values. -/
  let bvs ← match s.toList with
  | '0' :: 'x' :: rest => toBitVec32List rest []
  | _ => throw s!"Hex string must start with '0x', but got {s}."
  /- Concatenate the bitvecs to create a little-endian bytearray -/
  let data := bvs.foldr (fun new acc => (TensorLib.toLEByteArray new) ++ acc) ByteArray.empty
  pure {
    dtype := TensorLib.Dtype.int32,
    shape := Shape.mk [bvs.length],
    data
  }

/- Convert a list of tensors to a single tensor by concatenating them along a new first dimension. -/
def tensorOfTensorList (ns : List Tensor) : Compile Tensor :=
  match ns with
  | f :: r => do
    if ! (r.all fun t => t.shape == f.shape) then
      throw s!"All tensors in the list must have the same shape, but got {repr ns}."
    else if ! (r.all fun t => t.dtype == f.dtype) then
      throw s!"All tensors in the list must have the same dtype, but got {repr ns}."
    else
      let newShape := Shape.mk (ns.length :: f.shape.val)
      let dtype := f.dtype
      let size := ns.foldl (fun acc t => acc + t.size) 0
      let arr := Tensor.zeros dtype newShape
      let mut data := arr.data
      let mut posn := 0
      for t in ns do
        data := t.data.copySlice 0 data posn (t.data.size * size)
        posn := posn + (t.data.size * size)
      .ok { arr with data := data }
  | [] => pure (TensorLib.Tensor.empty TensorLib.Dtype.float32 (Shape.mk []))

/-
Parse a StableHLO string literal to a Tensor

Note that the meaning of string literals in StableHLO is not well-defined,
but in practice JAX uses them to hex encode integer tensors.
-/
def parseStringLiteral := parseInt32TensorFromHex
/- Parse a StableHLO boolean literal to a Bool. -/
def parseBoolLiteral : StableHLO.Parsing.BooleanLiteral → Bool
  | .true  => true
  | .false => false
/- Parse a StableHLO element literal to an TGR tensor. -/
def parseElementLiteral : StableHLO.Parsing.ElementLiteral → Compile TensorLib.Tensor
  | .floatLiteral f => f |> parseFloat |> TensorLib.Tensor.arrayScalarFloat32! |> pure
  | .stringLiteral s => s |> parseStringLiteral
  | .booleanLiteral b => b |> parseBoolLiteral |> TensorLib.Tensor.arrayScalarBool! |> pure
  | .complexLiteral _ =>  impossible "unimplemented"

/- Parse a StableHLO dense literal to an TGR tensor. -/
def parseTensorLiteral : StableHLO.Parsing.DenseLiteral → Compile Tensor
  /- special case for singleton tensors so we don't create an extra dimension -/
  | .denseElements [v] => do
    parseElementLiteral v
  | .denseElements l => do
    tensorOfTensorList (← l.mapM parseElementLiteral)
  | .denseDimension l => do
    tensorOfTensorList (← l.mapM parseTensorLiteral)

/- Convert a StableHLO tensor type to an TGR TensorTy. -/
def parseTensorType (t : StableHLO.Parsing.TensorType) : Compile TensorTy := do
    let shape ← t.shape.mapM (fun
      | .known d =>  pure d
      | .unknown => throw "Can't support tensors with dynamic shape")
    let dtype ← match t.tensorElementTypeGen with
      | .classic (.floatType .f32) => pure TensorLib.Dtype.float32
      | .classic (.floatType .f64) => pure TensorLib.Dtype.float64
      | .classic (.integerType {sign := .signed, size := .b8}) => pure TensorLib.Dtype.int8
      | .classic (.integerType {sign := .unsigned, size := .b8}) => pure TensorLib.Dtype.uint8
      | .classic (.integerType {sign := .signed, size := .b16}) => pure TensorLib.Dtype.int16
      | .classic (.integerType {sign := .unsigned, size := .b16}) => pure TensorLib.Dtype.uint16
      | .classic (.integerType {sign := .signed, size := .b32}) => pure TensorLib.Dtype.int32
      | .classic (.integerType {sign := .unsigned, size := .b32}) => pure TensorLib.Dtype.uint32
      | .classic (.integerType {sign := .signed, size := .b64}) => pure TensorLib.Dtype.int64
      | .classic (.integerType {sign := .unsigned, size := .b64}) => pure TensorLib.Dtype.uint64
      | .classic (.booleanType) => pure TensorLib.Dtype.bool
      | _ => throw s!"Unsupported tensor element type: {repr t.tensorElementTypeGen}"
    pure (.mk (.mk shape) dtype)

/- Parse an TGR TensorTy at index `n` from the list of types. -/
def parseTensorTypeFromValueTypes (l : List StableHLO.Parsing.ValueType) (n : Nat): Compile TensorTy :=
  match l[n]? with
  | .some (.tensorType t) => parseTensorType t
  | .some t => throw s!"Element {n} of type list must have tensor type, but got {repr t}."
  | _ => throw s!"Type list must have at least {n + 1} values, but got only {l.length}."

/- Parse an TGR TensorTy from a list of types, expecting the list to have exactly one element. -/
def parseSingleTensorTypeFromValueTypes : List StableHLO.Parsing.ValueType → Compile TensorTy
  | [.tensorType t] => parseTensorType t
  | t => throw s!"Expected type list to have a single tensor type, but got {repr t}."

/- Parse an array from a StableHLO literal. -/
def parseArray (c : StableHLO.Parsing.Literal) : Compile (List Nat) :=
  match c with
  | .array (.array64 arr) => pure (arr.map fun ⟨ _sign, n ⟩ => n)
  | .array (.array1 _) => throw "array1 unimplemented."
  | _ => throw "Expected an array of integers."

/-
Parse a Nat from a StableHLO float literal.
We need this because integers are often represented as floats in StableHLO.
-/
def parseNatFromElementLiteral (c : StableHLO.Parsing.Literal) : Compile Nat :=
  match c with
  | .element (.floatLiteral (.decimal {integerPart, fractionalPart, scientificPart})) =>
    match (fractionalPart.decimal == 0, scientificPart.decimal == 0, integerPart.sign) with
      | (true, true, .plus) => pure integerPart.decimal
      | (false, _, _) | (_, false, _) =>
        throw s!"Expected a non-negative integer, but got a float literal with fractional or scientific part: {repr c}."
      | (_, _, .minus) =>
        throw s!"Expected a non-negative integer, but got a float literal with negative sign: {repr c}."
  | .element (.floatLiteral l) => throw s!"Got unsupported float literal {repr l}."
  | l => throw s!"Expected a float literal but got {repr l}."

/- Find an attribute by name in a list of attributes -/
def lookupAttribute  (attrs : List StableHLO.Parsing.Attribute) (name : String) : Compile StableHLO.Parsing.Constant :=
  match attrs.find? (fun ⟨ id, _ ⟩ => id == name) with
  | some ⟨ _, attr ⟩ => pure attr
  | none => throw s!"Attribute '{name}' not found."

/- Find an attribute by name in a list of attributes, returning only the associated literal, not its type -/
def lookupAttributeValue (attrs : List StableHLO.Parsing.Attribute) (name : String) : Compile StableHLO.Parsing.Literal :=
  lookupAttribute attrs name |>.map (fun ⟨ lit, _ ⟩ => lit)

/- Get the value of a field in a StableHLO record, expecting it to be a list of integers. -/
def lookupNatsInFields (fields : List StableHLO.Parsing.StableHLORecordField) (name : String) : Compile (List Nat) :=
  match fields.find? (fun ⟨ n, _ ⟩ => n == name) with
  | some (.mk _ (.many ns)) => pure ns
  | some v => throw s!"Field '{name}' must be a list of integers, but got {repr v}."
  | none => pure []

/- Get the value of a field in a StableHLO record, expecting it to be a single integer. -/
def lookupNatInFields (fields : List StableHLO.Parsing.StableHLORecordField) (name : String) : Compile Nat :=
  match fields.find? (fun ⟨ n, _ ⟩ => n == name) with
  | some (.mk _ (.one n)) => pure n
  | some v => throw s!"Field '{name}' must be a single integer, but got {repr v}."
  | none => throw s!"Field '{name}' not found in record list {repr fields}."

/- extract the arguments to the `dotGeneral` operation from a record in the list of attributes -/
def extractDotDimensionNumbers (attrs : List StableHLO.Parsing.Attribute) : Compile (List Nat × List Nat × List Nat × List Nat) := do
  let dotAttr ← lookupAttributeValue attrs "dot_dimension_numbers"
  match dotAttr with
  | .stableHLORecord fields =>
    let lhs_batching_dims ← lookupNatsInFields fields "lhs_batching_dimensions"
    let lhs_contracting_dims ← lookupNatsInFields fields "lhs_contracting_dimensions"
    let rhs_batching_dims ← lookupNatsInFields fields "rhs_batching_dimensions"
    let rhs_contracting_dims ← lookupNatsInFields fields "rhs_contracting_dimensions"
    pure (lhs_batching_dims, lhs_contracting_dims, rhs_batching_dims, rhs_contracting_dims)
  | _ => throw "Attribute 'dot_dimension_numbers' must be a stableHLORecord."

/- extract the arguments to the `gather` operation from a record in the list of attributes -/
def extractDimensionNumbers (attrs : List StableHLO.Parsing.Attribute) : Compile (List Nat × List Nat × List Nat × Nat) := do
  let attr ← lookupAttributeValue attrs "dimension_numbers"
  match attr with
  | .stableHLORecord fields =>
    let offset_dims ← lookupNatsInFields fields "offset_dims"
    let collapsed_slice_dims ← lookupNatsInFields fields "collapsed_slice_dims"
    let start_index_map ← lookupNatsInFields fields "start_index_map"
    let index_vector_dim ← lookupNatInFields fields "index_vector_dim"
    pure (offset_dims, collapsed_slice_dims, start_index_map, index_vector_dim)
  | _ => throw "Attribute 'dimension_numbers' must be a stableHLORecord."

/-
The StableHLO `reduce` operation always calls an arbitrary reduction function.
However, in TGR we only support a few specific reduction operations (mostly
arithmetic and logical binary operators). Since many StableHLO programs only
use these basic reduction operations, we can recognize when the StableHLO function
called by a `reduce` operation is one of these basic operations, and convert it
to the corresponding TGR BinaryOp.
If this process is unsuccessful, it means that the input `reduce` function is more
complicated and can't be supported by the current TGR design.
-/
def reduceFunctionToReduceOp (f : StableHLO.Parsing.InputFunc) : Compile (BinaryOp) := do
  match f with
  | .mk _ [.stablehlo .maximum .., .return ..] => pure .max
  | .mk _ [.stablehlo .add .., .return ..] => pure .add
  | .mk _ [.stablehlo .and .., .return ..] => pure .and
  | .mk _ [.stablehlo op .., .return ..] => throw s!"Unimplemented reduction function {repr op}."
  | op =>
    throw ("Unable to recognize `reduce` function as simple binary operator. Compiling" ++
    "this program likely requires adding support for arbitrary function calling in `reduce`"
    ++ s!"Function: {repr op}")

/-
Compile a StableHLO operation into a list of TGR statements.

Note: this function annotates each statement with the type of its output,
but this type is merely passed through from the HLO program, not computed anew.
This means it's possible that if there's a mistake in the shape calculation
in the HLO program, the TGR statements will also have incorrect shapes.
Eventually, we'll want a function that can shape-check an TGR program.
-/
def compileOp  (op : StableHLO.Parsing.Operation) : Compile (List Statement) := do
  log s!"Compiling operation {repr op}"
  match op with
  | .stablehlo opCode inputValues inputFunctions inputAttributes outputs signature => do
    /- Reuse the variable names and shapes from the StableHLO program -/
    let output ← match outputs with
    | [output] => pure output
    | _ => throw "Operator signature must have a single output."
    let outputTy ← parseSingleTensorTypeFromValueTypes signature.range
    /- helper function to emit TGR for element-wise unary ops -/
    let makeUnOp := fun (op : UnaryOp) => do
      let a := inputValues[0]!
      pure [.assign output (.unaryOp op a) outputTy]
    /- helper function to emit TGR for element-wise binary ops -/
    let makeBinOp := fun (op : BinaryOp) => do
      let a := inputValues[0]!
      let b := inputValues[1]!
      pure [.assign output (.binaryOp op a b) outputTy]
    match opCode with
    /- element-wise unary operators -/
    | .sqrt => makeUnOp .sqrt
    | .negate => makeUnOp .neg
    | .exponential => makeUnOp .exp
    | .convert => makeUnOp (UnaryOp.convert outputTy.dtype)
    /- element-wise binary operators -/
    | .compare => makeBinOp .cmp
    | .multiply => makeBinOp .mul
    | .add => makeBinOp .add
    | .and => makeBinOp .and
    | .maximum => makeBinOp .max
    | .subtract =>  makeBinOp .sub
    | .divide =>  makeBinOp .div
    /- tensor nullary operators -/
    | .constant =>  do
      let valueAttr ← lookupAttributeValue inputAttributes "value"
      match valueAttr with
      | (.tensor t) => do
        let t ← parseTensorLiteral t
        if t.shape == Shape.empty then
          /- If the tensor is a scalar-array, we use a `full` operation
          to create a tensor of the same shape as the output. -/
          pure [.assign output (.full t outputTy.shape) outputTy]
        else
          /- If the tensor is not a scalar-array, it corresponds to a
          `const` operation. -/
          if t.shape.count != outputTy.shape.count then
            throw s!"Tensor literal shape {t.shape} does not match expected output shape {outputTy.shape}."
          let t ← t.reshape outputTy.shape
          pure [.assign output (.const t) outputTy]
      | _ => throw "Constant operation requires a 'value' attribute with tensor literal."
    /- tensor unary operators -/
    | .reshape => do
      let input := inputValues[0]!
      pure [.assign output (.reshape input outputTy.shape) outputTy]
    | .gather =>
      let (offsetDims, collapsedSliceDims, startIndexMap, indexVectorDim) ←
        extractDimensionNumbers inputAttributes
      let input := inputValues[0]!
      let indices := inputValues[1]!
      pure [.assign output (.gather input indices offsetDims collapsedSliceDims startIndexMap indexVectorDim) outputTy]
    | .slice =>
      let input := inputValues[0]!
      let start ← (← lookupAttributeValue inputAttributes "start_indices") |> parseArray
      let limit ← (← lookupAttributeValue inputAttributes "limit_indices") |> parseArray
      let stride ← (← lookupAttributeValue inputAttributes "strides") |> parseArray
      let slices ← start
        |> List.length
        |> List.range
        |> List.mapM (fun i =>
          TensorLib.Slice.make
            (.some $ Int.ofNat start[i]!)
            (.some $ Int.ofNat limit[i]!)
            (.some $ Int.ofNat stride[i]!))
      pure [.assign output (.slice input slices) outputTy]
    | .reduce =>
      let op ← reduceFunctionToReduceOp inputFunctions[0]!
      let dims ← (← lookupAttributeValue inputAttributes "dimensions") |> parseArray
      pure [.assign output (.reductionOp op inputValues[0]! inputValues[1]! dims) outputTy] -- TODO: init value
    | .broadcastInDim => do
      /-
      We compile a broadcast by first reshaping to a new tensor `t` with added
      dimensions of size 1 such that the rank is equal to the output rank, then
      we broadcast `t` to the output shape which expands some of those
      dimensions of size 1
      -/
      let input := inputValues[0]!
      let inputTy := ← parseTensorTypeFromValueTypes signature.domain 0
      let broadcastDims ← (← lookupAttributeValue inputAttributes "broadcast_dimensions") |> parseArray
      let reshaped ← gensym (input ++ "_reshaped")
      /- A shape that has the same number of dimensions as the output, but where
      specified dimensions match the input shape, and others are 1. -/
      let newShape := outputTy.shape.ndim |> List.range |> List.map (fun n =>
        if let .some i := broadcastDims.idxOf? n then
          inputTy.shape.val[i]!
        else
          1)
        |> .mk
      pure [
        .assign reshaped (.reshape input newShape) ⟨ newShape, inputTy.dtype ⟩,
        .assign output (.broadcast reshaped outputTy.shape) outputTy
      ]
    | .transpose => do
      let input := inputValues[0]!
      let dims ← (← lookupAttributeValue inputAttributes "permutation") |> parseArray
      pure  [.assign output (.transpose input dims) outputTy]
    /- tensor binary operators -/
    | .dotGeneral => do
      /-
      The semantics of the `dotGeneral` operation are complex, see the
      specification for details. The variables here are named similar to the
      variables in the spec to aid comprehension.
      https://github.com/openxla/stablehlo/blob/6f7b4ab8f96dc65cf3c8e9824836117d2934cc45/docs/spec.md?#dot_general
      -/
      /- Gather metadata from the inputs -/
      let (lhsBatchingDims, lhsContractingDims, rhsBatchingDims, rhsContractingDims) ←
        extractDotDimensionNumbers inputAttributes
      let lhs := inputValues[0]!
      let rhs := inputValues[1]!
      let lhsType ← parseTensorTypeFromValueTypes signature.domain 0
      let rhsType ← parseTensorTypeFromValueTypes signature.domain 1
      let dtype := lhsType.dtype
      let lhsShape := lhsType.shape
      let rhsShape := rhsType.shape
      let lhsDims :=  List.range (TensorLib.Shape.ndim lhsShape)
      let rhsDims :=  List.range (TensorLib.Shape.ndim rhsShape)
      /- Calculate shapes of intermediate tensors and output -/
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
      let batchSize := if batchShape.isEmpty then 1 else batchShape.foldl (· * ·) 1
      let resultShape := batchShape ++ lhsResultShape ++ rhsResultShape
      let lhsResultSize := if lhsResultShape.isEmpty then 1 else lhsResultShape.foldl (· * ·) (1 : Nat)
      let rhsResultSize := if rhsResultShape.isEmpty then 1 else rhsResultShape.foldl (· * ·) (1 : Nat)
      let contractingSize := if contractingShape.isEmpty then 1 else contractingShape.foldl (· * ·) 1
      /- Create fresh variable names for intermediate results -/
      let lhsTransposedName ← gensym (lhs ++ "_transposed")
      let rhsTransposedName ← gensym (rhs ++ "_transposed")
      let lhsReshapedName ← gensym (lhs ++ "_reshaped")
      let lhsReshapedShape := [batchSize, lhsResultSize, contractingSize]
      let lhsReshapedTy := TensorTy.mk (.mk lhsReshapedShape) dtype
      let rhsReshapedName ← gensym (rhs ++ "_reshaped")
      let rhsReshapedShape := [batchSize, rhsResultSize, contractingSize]
      let rhsReshapedTy := TensorTy.mk (.mk rhsReshapedShape) dtype
      let resultReshapedName ← gensym (output ++ "_reshaped")
      let resultReshapedShape := [batchSize, lhsResultSize, rhsResultSize]
      let resultReshapedType := TensorTy.mk (.mk resultReshapedShape) dtype
      /- Emit the TGR statements for the dotGeneral operation -/
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
      let tensors := inputValues
      let dim ← (← lookupAttributeValue inputAttributes "dimension") |> parseNatFromElementLiteral
      pure [.assign output (.concat tensors dim) outputTy]
    /- tensor ternary operators -/
    | .select =>
      let cond := inputValues[0]!
      let a := inputValues[1]!
      let b := inputValues[2]!
      pure [.assign output (.select cond a b) outputTy]
    | _ => throw s!"Unsupported HLO operation: {repr opCode}"
  | .return ops _ => do
    pure [Statement.ret ops]
  | .call callee inputValues outputs signature => do
    let output ← match outputs with
    | [output] => pure output
    | _ => throw "Call operator signature must have a single output."
    pure [
      Statement.assign
        output
        (.call callee inputValues)
        (← parseSingleTensorTypeFromValueTypes signature.range)]

  | s => throw s!"Unsupported operation type {repr s}"

def compileFunc (f : StableHLO.Parsing.Function) : Compile Unit := do
  let .mk args body := f.funcBody
  let inputs ← args.mapM (fun ⟨ name, v ⟩ => do
    match v with
    | .tensorType t => parseTensorType t
    | _ => throw s!"Function input {name} must have tensor type.")
  let outputs ← f.funcType.range.mapM fun
    | .tensorType t => parseTensorType t
    | _ => throw "Function output must be a tensor type."
  /- Since arguments are referred to by index, emit a statement for each
  argument that assigns it to a named variable -/
  let preamble ← args.mapIdxM (fun i ⟨ name, v ⟩ => do
    match v with
    | .tensorType t =>
      pure (Statement.assign name (.arg i) (← parseTensorType t))
    | _ => throw s!"Function input {name} must have tensor type.")
  let statements ← body.flatMapM compileOp
  let func := Function.mk f.funcId inputs outputs (preamble ++ statements)
  addFunction func

def compileModule (m : StableHLO.Parsing.Module) : Compile Unit :=
  m.modFuncs.forM compileFunc

def compile (m : List StableHLO.Parsing.Module) : (Except String Unit) × Ctx :=
  let compiled := match m with
    | [m] => compileModule m
    | _  => throw "Only one module is supported for now."
  match compiled.run default with
  | .ok _ s => (.ok (), s)
  | .error err s => (throw err, s)

end KLR.TGR.Compile
