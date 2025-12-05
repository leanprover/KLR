# KLR build container

Amazon Linux 2 (AL2) currently uses an old GLIBC version that is not supported by our Lean toolchain.
We provide a Docker image that can be used for development on AL2 and other unsupported platforms.

## Usage

The project root contains a simple wrapper script, `lakew`. Use `lakew` in place of `lake`:

```
$ ./lakew build
<...>
Build completed successfully (575 jobs).
$ ./lakew exe klr
klr [0.0.12]
KLR is an IR for NKI and other tensor-like languages in Lean.

USAGE:
    klr [SUBCOMMAND] [FLAGS]

FLAGS:
    -h, --help  Prints this message.
    --version   Prints the version.

SUBCOMMANDS:
    compile  Compile a NKI kernel
    gather   Gather Python sources into an AST file
    info     Display information about a KLR file
    trace    Trace Python to KLR
    list     List builtin functions and constants
```