#!/usr/bin/env bash
# Actual writer/reader publications and SQLite effects under the pinned SDK.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ "$(uname -sm)" = 'Linux x86_64' ] || { echo 'publication gate requires Linux x86-64' >&2; exit 1; }
[ "$(cat lean-toolchain)" = 'leanprover/lean4:v4.35.0' ] || { echo 'review SDK getter fixture for the changed toolchain' >&2; exit 1; }
command -v gdb >/dev/null
mkdir -p out/ref-publications
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build checkpoint_ack writer_resume prune_ack >out/ref-publications/build.log 2>&1
python3 tests/engine/ref_publications_negative.py
