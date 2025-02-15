import math

from apis import *

def tensor_split_kernel_(in_tensor, out_tensor_even, out_tensor_odd):
  """NKI kernel to split an input tensor into two output tensors, along the column axis.

  The even columns of the input tensor will be gathered into the first output tensor,
  and the odd columns of the input tensor will be gathered into the second output tensor.

  Args:
      in_tensor: an input tensor
      out_tensor_even: a first output tensor (will hold the even columns of the input tensor)
      out_tensor_odd: a second output tensor (will hold the odd columns of the input tensor)
  """

  # Extract tile sizes.
  sz_p, sz_f = in_tensor.shape
  sz_fout_even, sz_fout_odd = out_tensor_even.shape[1], out_tensor_odd.shape[1]

  # We assume that all three tensors have the same partition dimension size
  # and it does not exceed pmax
  assert in_tensor.shape[0] == out_tensor_even.shape[0] == out_tensor_odd.shape[0]
  assert in_tensor.shape[0] <= nl.tile_size.pmax

  # Make sure even/odd output tensors have correct free dimension size
  assert sz_fout_even == math.ceil(sz_f / 2)
  assert sz_fout_odd == math.floor(sz_f / 2)

  # Generate tensor indices for the input/output tensors
  i_p = nl.arange(sz_p)[:, None]
  i_f = nl.arange(sz_f)[None, :]
  i_fout_even = nl.arange(sz_fout_even)[None, :]
  i_fout_odd = nl.arange(sz_fout_odd)[None, :]

  # Split pattern:
  i_f_even = (2 * i_fout_even)
  i_f_odd = (2 * i_fout_odd + 1)

  # Load input data from external memory to on-chip memory
  in_tile = nl.load(in_tensor[i_p, i_f])

  # Perform the split
  # these assignments invoke copy instructions under the hood
  # which can execute on either Scalar or Vector Engine
  # (decided by compiler instruction scheduler)
  out_tile_even = in_tile[i_p, i_f_even]
  out_tile_odd = in_tile[i_p, i_f_odd]

  # Store the results back to external memory
  nl.store(out_tensor_even[i_p, i_fout_even], value=out_tile_even)
  nl.store(out_tensor_odd[i_p, i_fout_odd], value=out_tile_odd)


def tensor_maxpool_kernel_(in_tensor, out_tensor, pool_size):
  """NKI kernel to compute a 2D max-pool operation

  Args:
      in_tensor: an input tensor, of dimensions C x H x W
      pool_size: integer P representing a (square) pool-window size
      out_tensor: the resulting output tensor, of dimensions C x (H/P) x (W/P)
  """

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
  # We use numpy's advanced indexing, in order to extend in_tile to 5D, and then reduce-max two dimension.
  # axis[0] is the index for p_dim, and thus doesn't participate in the reduction operation.
  # axis[1] and axis[2] together index the rows, with axis[2] responsible for inner strides
  # (i.e. inside a pooling window), and axis[1] responsible for the outer strides. As such, we reduce over axis[2].
  # Similarly, axis[3] and axis[4] together index the columns, and we thus reduce over axis[4].
  out_tile = nl.max(in_tile[i_0, sz_pool*i_1+i_2, sz_pool*i_3+i_4], axis=[2,4])

  # Store the results back to external memory
  nl.store(out_tensor[i_p, i_hout, i_wout], value=out_tile)
