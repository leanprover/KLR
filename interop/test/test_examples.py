import pytest
import numpy as np

from examples import *
from klr.frontend import Kernel


@pytest.mark.parametrize("module,name",
    [ (getting_started, "nki_tensor_add_kernel"),
      (layout, "tensor_exp_kernel_1"),
      (layout, "tensor_exp_kernel_2"),
      (index, "tensor_split_kernel_"),
      (index, "tensor_maxpool_kernel_"),
      (mm, "matmul_128x128x512_spmd_nisa"),
      (mm, "matmul_128x128x512_nl"),
      (prof, "tensor_exp_kernel_"),
      (average_pool, "tensor_avgpool_kernel_"),
      (fused_mamba, "mamba_v1"),
      (fused_mamba, "mamba_v2"),
      (fused_mamba, "mamba_v3"),
      (layernorm, "nki_layernorm_kernel_v1"),
      (layernorm, "nki_layernorm_kernel_v2"),
      (matmul, "nki_matmul_basic_"),
      (matmul, "nki_matmul_tiled_"),
      (matmul, "nki_matmul_hoist_load_"),
      (matmul, "nki_matmul_block_free_dimension_"),
      (matmul, "nki_matmul_fully_optimized_"),
      (rmsnorm, "nki_rmsnorm_kernel"),
      (sd_attention, "fused_self_attn_for_SD_small_head_size"),
      (tensor_addition, "nki_tensor_add_kernel_"),
      (tensor_addition, "nki_tensor_add"),
      (transpose2d, "tensor_transpose2D_kernel_")
    ])


def test_parse(module, name):
  f = getattr(module, name)
  K = Kernel(f)
  print(K)


if __name__ == '__main__':
  module, name = getting_started, "nki_tensor_add_kernel"
  a = np.ndarray((128,512))
  f = getattr(module, name)
  K = Kernel(f)
  K.specialize((a,a,a))
  print(K)
