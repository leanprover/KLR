# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import json
from tempfile import NamedTemporaryFile
from typing import Optional, Sequence, Union

from . import frontend

class NKIObject:
    pass

# wrapper around kernel.specialize()
def _specialize_kernel(
    kernel: frontend.Kernel,
    args: Optional[tuple] = None,
    kwargs: Optional[dict] = None,
    *,
    grid: Optional[int] = None,
    schedule: Optional[Sequence[tuple[str, Union[str, Sequence[str]]]]] = None,
):
    metadata_json_str = kernel.specialize(args, kwargs, grid, schedule)
    metadata = json.loads(metadata_json_str)
    return metadata

# wrapper around tracing step via KLR's Lean FFI.
def _trace_kernel(
    kernel: frontend.Kernel,
    *,
    dst_filepath: str,
) -> dict:
    """
    Trace Python to KLIR

    Returns: dict of metadata
    """
    metadata_json_str = kernel.trace(dst_filepath)
    metadata = json.loads(metadata_json_str)
    return metadata
