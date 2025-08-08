/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
https://docs.python.org/3/reference/grammar.html
-/

import KLR.NKI.Typed.Python.PrettyPrint
import KLR.NKI.Typed.Python.Parser

open KLR.NKI.Typed.Python

/--
info: from neuronxcc import nki

import neuronxcc.nki.language as nl

@nki.jit
def nki_tensor_add_kernel(a_input, b_input):
  "NKI kernel to compute element-wise addition of two input tensors
      "
  print("\"\'a")
  print("\"\'a")
  assert a_input.shape == b_input.shape
  assert a_input.shape[0] <= nl.tile_size.pmax
  a_tile = nl.load(a_input)
  b_tile = nl.load(b_input)
  c_tile = nl.add(a_tile, b_tile)
  c_output = nl.ndarray(a_input.shape, dtype=a_input.dtype, buffer=nl.shared_hbm)
  nl.store(c_output, value=c_tile)
  return c_output
-/
#guard_msgs in #eval Parser.run "
from neuronxcc import nki
import neuronxcc.nki.language as nl


@nki.jit
def nki_tensor_add_kernel(a_input, b_input):

    \"\"\"NKI kernel to compute element-wise addition of two input tensors
    \"\"\"
    print(\"\\\"'a\")
    print(\'\\\"\\\'a\')

    # Check all input/output tensor shapes are the same for element-wise operation
    assert a_input.shape == b_input.shape

    # Check size of the first dimension does not exceed on-chip memory tile size limit,
    # so that we don't need to tile the input to keep this example simple
    assert a_input.shape[0] <= nl.tile_size.pmax

    # Load the inputs from device memory to on-chip memory
    a_tile = nl.load(a_input)
    b_tile = nl.load(b_input)

    # Specify the computation (in our case: a + b)
    c_tile = nl.add(a_tile, b_tile)

    # Create a HBM tensor as the kernel output
    c_output = nl.ndarray(a_input.shape, dtype=a_input.dtype, buffer=nl.shared_hbm)

    # Store the result to c_output from on-chip memory to device memory
    nl.store(c_output, value=c_tile)

    # Return kernel output as function output
    return c_output

"

/--
info: "
Copyright (C) 2024, Amazon.com. All Rights Reserved

NKI implementation for average pool 2D NKI tutorial.

"

def tensor_avgpool_kernel_(in_tensor, out_tensor, pool_size):
  "NKI kernel to compute a 2D avg-pool operation
  
    Args:
        in_tensor: an input tensor, of shape C x H x W
        pool_size: an integer representing a (square) pool-window size
        out_tensor: the resulting output tensor, of shape C x (H/pool_size) x (W/pool_size)
    "
  sz_cin, sz_hin, sz_win = in_tensor.shape
  sz_cout, sz_hout, sz_wout = out_tensor.shape
  assert sz_cin == sz_cout
  sz_p = sz_cin
  sz_pool = pool_size
  i_p = nl.arange(sz_p)[:, None, None]
  i_win = nl.arange(sz_win)[None, None, :]
  i_hin = nl.arange(sz_hin)[None, :, None]
  i_wout = nl.arange(sz_wout)[None, None, :]
  i_hout = nl.arange(sz_hout)[None, :, None]
  i_0 = nl.arange(sz_p)[:, None, None, None, None]
  i_1 = nl.arange(sz_hin // sz_pool)[None, :, None, None, None]
  i_2 = nl.arange(sz_pool)[None, None, :, None, None]
  i_3 = nl.arange(sz_win // sz_pool)[None, None, None, :, None]
  i_4 = nl.arange(sz_pool)[None, None, None, None, :]
  in_tile = nl.ndarray([sz_p, sz_hin, sz_win], dtype=in_tensor.dtype)
  in_tile[:, :, :] = nl.load(in_tensor[i_p, i_hin, i_win])
  out_tile = nl.sum(in_tile[i_0, sz_pool * i_1 + i_2, sz_pool * i_3 + i_4], axis=[2, 4]) / (pool_size * pool_size)
  nl.store(out_tensor[i_p, i_hout, i_wout], value=out_tile)

def np_average_pool_2D(in_tensor, pool_size):
  c, h_in, w_in = in_tensor.shape
  reshaped = in_tensor.reshape(c, h_in // pool_size, pool_size, w_in // pool_size, pool_size)
  return np.nanmean(reshaped, axis=(2, 4))
-/
#guard_msgs in #eval Parser.run "
\"\"\"
Copyright (C) 2024, Amazon.com. All Rights Reserved

NKI implementation for average pool 2D NKI tutorial.

\"\"\"

def tensor_avgpool_kernel_(in_tensor, out_tensor, pool_size):
  \"\"\"NKI kernel to compute a 2D avg-pool operation

  Args:
      in_tensor: an input tensor, of shape C x H x W
      pool_size: an integer representing a (square) pool-window size
      out_tensor: the resulting output tensor, of shape C x (H/pool_size) x (W/pool_size)
  \"\"\"

  # Get input/output dimensions
  sz_cin, sz_hin, sz_win = in_tensor.shape
  sz_cout, sz_hout, sz_wout = out_tensor.shape
  assert sz_cin == sz_cout

  # Set relevant sizes
  sz_p = sz_cin
  sz_pool = pool_size

  # Generate tensor h/w index patterns
  # 3D indexing according to [C, H, W]
  i_p = nl.arange(sz_p)[:, None, None] # 3D for
  i_win = nl.arange(sz_win)[None, None, :]
  i_hin = nl.arange(sz_hin)[None, :, None]

  i_wout = nl.arange(sz_wout)[None, None, :]
  i_hout = nl.arange(sz_hout)[None, :, None]

  # Generate pool index patterns (requires two extra dimensions, for the pool window)
  i_0 = nl.arange(sz_p)[:, None, None, None, None] #
  i_1 = nl.arange(sz_hin//sz_pool)[None, :, None, None, None] # y_outer
  i_2 = nl.arange(sz_pool)[None, None, :, None, None] # y_inner
  i_3 = nl.arange(sz_win//sz_pool)[None, None, None, :, None] # x_outer
  i_4 = nl.arange(sz_pool)[None, None, None, None, :] # x_inner

  # Load input data from external memory to on-chip memory
  # Declare ndarray to force a 3D tensor (temporary requirement)
  in_tile = nl.ndarray([sz_p, sz_hin, sz_win], dtype=in_tensor.dtype)
  in_tile[:,:,:] = nl.load(in_tensor[i_p, i_hin, i_win])

  # Perform the pooling operation:
  # We use numpy's advanced indexing, in order to extend in_tile to 5D, and then reduce-average two dimension.
  # axis[0] is the index for p_dim, and thus doesn't participate in the reduction operation.
  # axis[1] and axis[2] together index the rows, with axis[2] responsible for inner strides
  # (i.e. inside a pooling window), and axis[1] responsible for the outer strides. As such, we reduce over axis[2].
  # Similarly, axis[3] and axis[4] together index the columns, and we thus reduce over axis[4].
  out_tile = nl.sum(in_tile[i_0, sz_pool*i_1+i_2, sz_pool*i_3+i_4], axis=[2,4]) / (pool_size*pool_size)

  # Store the results back to external memory
  nl.store(out_tensor[i_p, i_hout, i_wout], value=out_tile)


# Reference NumPy implementation
def np_average_pool_2D(in_tensor, pool_size):
  c, h_in, w_in = in_tensor.shape
  reshaped = in_tensor.reshape(c, h_in // pool_size, pool_size, w_in // pool_size, pool_size)
  return np.nanmean(reshaped, axis=(2, 4))

"
