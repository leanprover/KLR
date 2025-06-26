# C/C++ Front-end

This directory contains a C/C++ version of the KLR front-end for NKI. The main
entry point is `frontend.c` which defines a python extension module and a type
called `Kernel` which provides the API for the front-end. The typical use of
this API will create a new `Kernel` type from a user's python function,
serialize the result, and later deserialize to Python types:

```python
import frontend
K = frontend(kernel)
K.specialize(arguments)
bytes = K.serialize()
...
nki_ast = frontend.deserialize(bytes)
```

## Lean Generated Files

The following files have been generated from Lean sources.

| C File | Lean Source | Method |
|-|-|-|
| ast_common.h           | KLR/Serde/File.lean  | KLR/Extract/C |
| ast_file.h             | KLR/File.lean        | KLR/Extract/C |
| ast_python_core.h      | KLR/Python.lean      | KLR/Extract/C |
| ast_nki.h              | KLR/NKI/Basic.lean   | KLR/Extract/C |
| ast_nki.py             | KLR/NKI/Basic.lean   | KLR/Extract/Python |
| serde_common.[hc]      | KLR/Serde/File.lean  | KLR/Extract/Serde |
| serde_file.[hc]        | KLR/File.lean        | KLR/Extract/Serde |
| serde_python_core.[hc] | KLR/Python.lean      | KLR/Extract/Serde |
| serde_nki.[hc]         | KLR/NKI/Basic.lean   | KLR/Extract/Serde |

## CPython Sources

The files in the `peg_parser` directory are from the CPython sources. These
files have been lightly modified for use in NKI. The modifications are mostly
marking functions as `static` and removing unused code. See comments in
`peg_parser.c` for more details.

### Generating PEG Parser files

Several of the source files are generated from the parser generator in the
CPython source tree. The source for generating these files is the `Token` and
`python.gram` files (contained here) and the `Python.asdl` files in the CPython
sources.

The following commands can be used to generate derived sources.

Files: `peg_parser/ast_python.c` and `ast_python.h`
```sh
$PYSRC/Parser/asdl_c.py -d $PYSRC/Parser/Python.asdl \
  -C peg_parser/ast_python.c -H ast_python.h -i ignored
rm ignored
```

Files: `peg_parser/token.c`
```sh
python $PYSRC/Tools/build/generate_token.py h Tokens tmp1
python $PYSRC/Tools/build/generate_token.py c Tokens tmp2
cat tmp1 tmp2 > peg_parser/token.c
rm tmp1 tmp2
```

Files: `peg_parser/parser.c`
```sh
PYTHONPATH=$PYSRC/Tools/peg_generator \
  python3 -m pegen -q c python.gram Tokens -o peg_parser/parser.c
```

