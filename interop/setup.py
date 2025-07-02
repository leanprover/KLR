from setuptools import Extension, setup
import os
import sys

# MACOSX_DEPLOYMENT_TARGET tells compiler the oldest macOS version to support.
# It also determines the "macosx_13_0" part of the wheel name,
# and pip won't install that wheel on macOS older than that.
# If we don't set MACOSX_DEPLOYMENT_TARGET explicitly, setuptools will set
# it to whatever your python installation was built with,
# and if you used the python.org installer it's something ancient like 10.9,
# which causes compiler warnings about modern-ish things like aligned_alloc().
if sys.platform == 'darwin' and not os.getenv('MACOSX_DEPLOYMENT_TARGET'):
  os.environ['MACOSX_DEPLOYMENT_TARGET'] = '13.0'

# Note, because we are building an extension module, we will get arch specific wheels.
# This is important because we are putting an arch-specific binary into the wheel
# as an "extra" file.
#
# TODO: move this to pyproject.toml once Brazil supports newer versions of setuptools
setup(
  ext_modules=[
    Extension(
      name="klr.frontend",
      sources=[
        "klr/cbor.c",
        "klr/frontend.c",
        "klr/gather.c",
        "klr/peg_parser.c",
        "klr/region.c",
        "klr/serde.c",
        "klr/serde_common.c",
        "klr/serde_file.c",
        "klr/serde_nki.c",
        "klr/serde_python_core.c",
        "klr/simplify.c",
        "klr/topy_nki.c",
      ],
    ),
  ],
)
