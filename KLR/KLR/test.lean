-- Test file demonstrating usage of the NKI ISA Lean definitions

import TestIsa.ISA

open NKI.ISA

-- Example tile definitions
def example_tile_sbuf : Tile := {
  shape := { partition_axis := 128, free_axes := [512] },
  dtype := DataType.float32,
  buffer := BufferType.sbuf
}

def example_tile_psum : Tile := {
  shape := { partition_axis := 128, free_axes := [128] },
  dtype := DataType.bfloat16,
  buffer := BufferType.psum
}

def small_tile : Tile := {
  shape := { partition_axis := 32, free_axes := [64] },
  dtype := DataType.float16,
  buffer := BufferType.sbuf
}

-- Example 1: Simple activation instruction
def relu_activation : Instruction :=
  Instruction.activation
    ActivationFunc.relu           -- ReLU activation
    example_tile_sbuf            -- Input data
    none                         -- No bias
    (Operand.scalar 1.0)         -- Scale of 1.0
    none                         -- No reduction operation
    none                         -- No reduction result
    ReduceCmd.idle               -- Don't use accumulators
    Mask.none                    -- No mask
    none                         -- Use same dtype as input

-- Example 2: Matrix multiplication
def matmul_example : Instruction :=
  Instruction.nc_matmul
    example_tile_sbuf            -- Stationary operand
    example_tile_sbuf            -- Moving operand
    false                        -- Not ones/zeros only
    false                        -- Not ones/zeros only
    false                        -- Not transpose
    none                         -- No tile position specified
    none                         -- No tile size specified
    Mask.none                    -- No mask

-- Example 3: Tensor-scalar operation (multiply by 2.0 then add 1.0)
def tensor_scalar_example : Instruction :=
  Instruction.tensor_scalar
    example_tile_sbuf            -- Input data
    MathOp.multiply              -- First operation: multiply
    (Operand.scalar 2.0)         -- Multiply by 2.0
    false                        -- Normal order (data * 2.0)
    (some MathOp.add)            -- Second operation: add
    (some (Operand.scalar 1.0))  -- Add 1.0
    false                        -- Normal order
    none                         -- Use same dtype as input
    Mask.none                    -- No mask
    Engine.unknown               -- Let compiler choose engine

-- Example 4: Tensor reduction (sum along axis 1)
def reduce_example : Instruction :=
  Instruction.tensor_reduce
    MathOp.add                   -- Sum reduction
    example_tile_sbuf            -- Input data
    [1]                          -- Reduce along axis 1 (free dimension)
    Mask.none                    -- No mask
    none                         -- Use same dtype as input
    false                        -- Don't negate result
    false                        -- Don't keep dimensions

-- Example 5: DMA copy with error handling
def dma_copy_example : Instruction :=
  Instruction.dma_copy
    example_tile_psum            -- Destination
    example_tile_sbuf            -- Source
    Mask.none                    -- No mask
    none                         -- No read-modify-write
    OobMode.error                -- Error on out-of-bounds
    DgeMode.unknown              -- Let compiler choose DGE mode

-- Example 6: Dropout with 0.1 probability
def dropout_example : Instruction :=
  Instruction.dropout
    example_tile_sbuf            -- Input data
    (Operand.scalar 0.1)         -- 10% dropout probability
    Mask.none                    -- No mask
    none                         -- Use same dtype as input

-- Example 7: Memory initialization
def memset_example : Instruction :=
  Instruction.memset
    { partition_axis := 64, free_axes := [256] }  -- Shape
    0.0                          -- Initialize to zero
    DataType.float32             -- Float32 data type
    Mask.none                    -- No mask
    Engine.unknown               -- Let compiler choose engine

-- Example 8: Transpose operation
def transpose_example : Instruction :=
  Instruction.nc_transpose
    small_tile                   -- Input data (32x64)
    Mask.none                    -- No mask
    none                         -- Use same dtype as input
    Engine.tensor                -- Use tensor engine

-- Example 9: Complex activation with bias and scale
def complex_activation : Instruction :=
  Instruction.activation
    ActivationFunc.gelu          -- GELU activation
    example_tile_sbuf            -- Input data
    (some (Operand.vector small_tile))  -- Bias vector
    (Operand.scalar 0.5)         -- Scale by 0.5
    (some MathOp.add)            -- Reduction operation
    (some small_tile)            -- Store reduction result
    ReduceCmd.reset_reduce       -- Reset then accumulate
    Mask.none                    -- No mask
    (some DataType.float16)      -- Output as float16

-- Example 10: Tensor-tensor element-wise operation
def tensor_add_example : Instruction :=
  Instruction.tensor_tensor
    example_tile_sbuf            -- First operand
    example_tile_sbuf            -- Second operand
    MathOp.add                   -- Element-wise addition
    none                         -- Use input dtype
    Mask.none                    -- No mask
    Engine.vector                -- Use vector engine

-- Function to demonstrate pattern matching on instructions
def get_instruction_type (inst : Instruction) : String :=
  match inst with
  | Instruction.activation _ _ _ _ _ _ _ _ _ => "Activation"
  | Instruction.nc_matmul _ _ _ _ _ _ _ _ => "Matrix Multiplication"
  | Instruction.tensor_scalar _ _ _ _ _ _ _ _ _ _ => "Tensor-Scalar Operation"
  | Instruction.tensor_reduce _ _ _ _ _ _ _ => "Tensor Reduction"
  | Instruction.dma_copy _ _ _ _ _ _ => "DMA Copy"
  | Instruction.dropout _ _ _ _ => "Dropout"
  | Instruction.memset _ _ _ _ _ => "Memory Set"
  | Instruction.nc_transpose _ _ _ _ => "Transpose"
  | Instruction.tensor_tensor _ _ _ _ _ _ => "Tensor-Tensor Operation"
  | _ => "Other Operation"

-- Test the pattern matching function
#eval get_instruction_type relu_activation        -- Should output "Activation"
#eval get_instruction_type matmul_example         -- Should output "Matrix Multiplication"
#eval get_instruction_type tensor_scalar_example  -- Should output "Tensor-Scalar Operation"

-- Function to count total number of instruction types
def count_instruction_variants : Nat := 32  -- Based on our Instruction inductive type

-- Helper function to check if an instruction uses a specific engine
def uses_engine (inst : Instruction) (eng : Engine) : Bool :=
  match inst with
  | Instruction.tensor_scalar _ _ _ _ _ _ _ _ _ engine => engine == eng
  | Instruction.tensor_copy _ _ _ engine => engine == eng
  | Instruction.nc_transpose _ _ _ engine => engine == eng
  | Instruction.tensor_tensor _ _ _ _ _ engine => engine == eng
  | Instruction.memset _ _ _ _ engine => engine == eng
  | _ => false

-- Example usage of the helper function
#eval uses_engine tensor_scalar_example Engine.unknown  -- Should be true
#eval uses_engine transpose_example Engine.tensor       -- Should be true

-- Demonstrate creating a sequence of instructions (like a program)
def example_program : List Instruction := [
  memset_example,      -- Initialize memory
  relu_activation,     -- Apply ReLU activation
  matmul_example,      -- Perform matrix multiplication
  reduce_example,      -- Reduce the result
  dma_copy_example     -- Copy result to destination
]

-- Function to get program length
def program_length : Nat := example_program.length

#eval program_length  -- Should output 5

-- Show that we can work with the data structures
#eval example_tile_sbuf.dtype                    -- DataType.float32
#eval example_tile_sbuf.shape.partition_axis     -- 128
#eval example_tile_sbuf.buffer                   -- BufferType.sbuf
