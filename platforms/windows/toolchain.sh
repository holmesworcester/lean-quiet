#!/usr/bin/env bash
# Pinned official Lean runtime, compiler, headers and libraries for x64 Windows.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
base=out/toolchain
archive=$base/lean-windows.tar.zst
mkdir -p "$base"
if [ ! -f "$archive" ]; then
  curl -fL --retry 3 -o "$archive.tmp" https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-windows.tar.zst
  mv "$archive.tmp" "$archive"
fi
echo "c07e88d1fe4839ec96a79f54637b2a3a983ea6c5b7e82ff35afa22a7700a86b7  $archive" | sha256sum -c -
if [ ! -d "$base/lean-4.34.0-windows" ]; then tar --zstd -xf "$archive" -C "$base"; fi
