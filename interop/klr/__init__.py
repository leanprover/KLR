# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Paul Govereau, Sean McLaughlin

import json
from tempfile import NamedTemporaryFile
from typing import Optional, Sequence, Union

from . import frontend


# wrapper around kernel.specialize()
def _specialize_kernel(
    kernel: frontend.Kernel,
    args: Optional[tuple] = None,
    kwargs: Optional[dict] = None,
    *,
    grid: Optional[int] = None,
    schedule: Optional[Sequence[tuple[str, Union[str, Sequence[str]]]]] = None,
):
    kernel.specialize(args, kwargs, grid, schedule)


# wrapper around tracing step via KLR's Lean FFI.
# (Using the Lean impl because it's currently more mature than the C impl).
def _trace_kernel(
    kernel: frontend.Kernel,
    *,
    dst_filepath: str,
) -> dict:
    """
    Trace Python to KLIR

    Returns: dict of metadata
    """

    # The current trace function needs to read in a file with the Python AST.
    # Then it writes out a file with the final KLIR.

    # So first we need to create that file with the Python AST...
    with NamedTemporaryFile(suffix="_python_ast.klir", delete=False) as tmp:
        python_ast_filepath = tmp.name
    kernel._serialize_python(python_ast_filepath)

    # OK. Now we can invoke trace() which writes out the final KLIR to a file...
    metadata_json_str = frontend._klr_trace(python_ast_filepath, dst_filepath)

    # trace() returned metadata as a string of JSON data.
    # Return it as a Python dict
    metadata = json.loads(metadata_json_str)
    return metadata
