# Kernel Language Representation (KLR)

This repository contains an implementation of KLR, a core language and
elaborators for machine learning kernels. The goal of KLR is to define a common
representation for kernel functions with a precise formal semantics along with
translations from common kernel languages to the KLR core language. The initial
focus of KLR is the
[Neuron Kernel Interface](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/nki/index.html),
and the [Trainium](https://aws.amazon.com/ai/machine-learning/trainium/) hardware.


# Quick Start

The easiest way to get started using KLR is to install the python package
using `pip`:

```
# pip install klr-lang
# python -m klr nki-to-klr test.py test_kernel -o test_kernel.klr
# python -m klr parse-klr test_kernel.klr
```

For more information see the [Getting Started Guide](docs/getting_started.md)

# Interop

The KLR compiler starts with Python code (e.g. NKI kernels), converts the source
code to JSON and passes it to the Lean parser. The lean parser converts (aka
traces) the Python AST into KLR. As such, we have an external dependency on
a Python runtime. To keep these processes as separate as possible, we just use
a simple file-IO pipeline;

  1. Python parser parses kernel.py to JSON (using reflection)
  2. Python writes kernel.json
  3. KLR reads kernel.json
  4. KLR writes klr.json
  5. Python reads klr.json into a data structure


# Steps to make a new version/wheel

1. Bump the build or minor version in
- interop/pyproject.toml (Deployment to PyPI will fail if you forget this.)
- Main.klrCmd (Nothing will break if you don't, but we'd like to be consistent)
2. Create a git tag of the form v1.2.3 and push it to KLR repo

This should trigger a build that uploads the artifacts to pypi.
