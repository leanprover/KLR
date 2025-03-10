
Python bindings for KLR

# Usage

# Note

There are 3 files in our `nki` Python package. These are KLR implementations of the corresponding files from the Neuron SDK repo:

* [nki/__init__.py](https://github.com/aws-neuron/aws-neuron-sdk/blob/master/general/nki/api/nki/__init__.py)
* [nki/isa/__init__.py](https://github.com/aws-neuron/aws-neuron-sdk/blob/master/general/nki/api/nki/isa/__init__.py)
* [nki/language/__init__.py](https://github.com/aws-neuron/aws-neuron-sdk/blob/master/general/nki/api/nki/language/__init__.py)

We do this to remove a dependency on the `neuronxcc` Python package that does not build on OSX.

# TODO

1. Automatically sync `nki` API directories with the `neuronxcc` package.
   The later does not install on OSX, and we generally don't want to
   require it since it's large and unnecessary.

2. Automatically sync `nki` examples with the github examples

# Notes

I keep getting __pycache__ directories created in the source tree, even with

    export PYTHONDONTWRITEBYTECODE=1

This is annoying.
