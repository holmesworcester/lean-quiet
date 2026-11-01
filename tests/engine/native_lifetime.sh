#!/usr/bin/env bash
# Linux x86-64, GDB with child ptrace, localhost TCP, pinned Lean 4.34.0.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ "$(uname -sm)" = 'Linux x86_64' ] || { echo 'native lifetime gate requires Linux x86-64' >&2; exit 1; }
[ "$(cat lean-toolchain)" = 'leanprover/lean4:v4.34.0' ] || { echo 'review SDK getter fixture for the changed toolchain' >&2; exit 1; }
command -v gdb >/dev/null
mkdir -p out/native-lifetime
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build native_lifetime stop_flag reader_stop >out/native-lifetime/build.log 2>&1
python3 tests/engine/native_lifetime_negative.py
