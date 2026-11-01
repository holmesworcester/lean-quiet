#!/usr/bin/env bash
# Pinned official Lean runtime, compiler, headers and libraries for x64 Windows.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
base=out/toolchain
archive=$base/lean-4.35.0-windows.tar.zst
mkdir -p "$base"
if [ ! -f "$archive" ]; then
  curl -fL --retry 3 -o "$archive.tmp" https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-windows.tar.zst
  mv "$archive.tmp" "$archive"
fi
echo "893fde3f52b48c647e3edcf33844cbb61f8ef70fcd88e0536bfc83f29844081e  $archive" | sha256sum -c -
if [ ! -d "$base/lean-4.35.0-windows" ]; then tar --zstd -xf "$archive" -C "$base"; fi
