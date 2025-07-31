#!/bin/bash
set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: $0 NKI_REPO_DIR"
    echo "Copy C files from .lake/**/*.c to the NKI repo, to be built as C."
    echo "You can copy over the network like:"
    echo "./copy-lean-c-to-nki.sh my-dev-dsk-alias:/workplace/myname/myworkspace/src/NeuronKernelInterface"
    exit 1
fi

NKI_REPO_DIR="$1"

SRC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ ! -d "$SRC_DIR/.lake" ]; then
    echo "Error: $SRC_DIR/.lake directory not found."
    echo "You must first run: lake build"
    exit 1
fi


DST_DIR="$NKI_REPO_DIR/src/nki/_klr/_ext/lean_c"

copy_c_files() {
    local src="$1"
    local dst="$2"
    # Copy all .c files (except Main.c, because we just want libs not exes)
    (set -x; rsync \
        --archive \
        --verbose \
        --prune-empty-dirs \
        --no-motd \
        --include="*/" \
        --include="*.c" \
        --exclude="*" \
        "$src/" \
        "$dst/")
}

# copy KLR
copy_c_files "$SRC_DIR/.lake/build/ir" "$DST_DIR/KLR"
# there's a separate lakefile for KLR.Util, so it ends up in a different build dir,
# but merge it in with the rest of the KLR code from the previous step
copy_c_files "$SRC_DIR/KLR/.lake/build/ir/Util" "$DST_DIR/KLR/KLR/Util"

# copy dependencies
copy_c_files "$SRC_DIR/.lake/packages/aesop/.lake/build/ir" "$DST_DIR/Aesop"
copy_c_files "$SRC_DIR/.lake/packages/batteries/.lake/build/ir" "$DST_DIR/Batteries"
copy_c_files "$SRC_DIR/.lake/packages/plausible/.lake/build/ir" "$DST_DIR/Plausible"
copy_c_files "$SRC_DIR/.lake/packages/TensorLib/.lake/build/ir" "$DST_DIR/TensorLib"

echo "SUCCESS!"
exit 0
