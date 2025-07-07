# Kernel Language Representation (KLR)

This repository contains an implementation of KLR, a core language and
elaborators for machine learning kernels. The goal of KLR is to define a common
representation for kernel functions with a precise formal semantics along with
translations from common kernel languages to the KLR core language. The initial
focus of KLR is the
[Neuron Kernel Interface](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/index.html),
and the [Trainium](https://aws.amazon.com/ai/machine-learning/trainium/) hardware.

# Building on Amazon Linux 2023

To build the FFI utilities like Archive, please use

LIBRARY_PATH=/usr/lib64 lake build

(or export the path) to get linking to work correctly.

# Quick Start

The easiest way to get started using KLR is to install the python package
using `pip`:

```
# pip install klr-lang
# klr gather test.py test_kernel -o test_kernel.klr
# klr trace test_kernel.klr
```

For more information see the [Getting Started Guide](docs/getting_started.md)

# Interop with Python

The KLR compiler starts with Python code (e.g. NKI kernels), and converts this
into an instance of the abstract syntax tree found in `KLR/Python.lean`. The
current version of KLR uses the CPython parser to do this conversion. The
parsing processes is called "gather" and involves the following steps:

  1. Load the Python interpreter with our custom CPython extension module
  2. Find the kernel function and extract its source code
  3. Run the CPython parser
  4. Transform the CPython AST to our Python AST
  5. Repeat steps 2-5 for all found references
  6. Serialize the AST to the KLR on-disk format
  7. From Lean, deserialize the Python AST from the on-disk format

This process is complex and brittle, and will be replaced by a proper (pure
Lean) parser in future versions of KLR.

# Steps to make a new version/wheel

1. Bump the build or minor version in
- interop/pyproject.toml (Deployment to PyPI will fail if you forget this.)
- Main.klrCmd (Nothing will break if you don't, but we'd like to be consistent)
2. Create a git tag of the form v1.2.3 and push it to KLR repo

This should trigger a build that uploads the artifacts to pypi.

# Adding a new Lake package

If you want to add a new directory with its own lakefile,
please ensure you (relative) symlink lean-toolchain to that directory.
Otherwise the VSCode plugin will use the top level directory
lakefile.
