#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/retry-admission
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.wire.RetryOrderLaws retry_multiplex >out/retry-admission/build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/vacuity/RetryOrder.lean >out/retry-admission/kernel-witness.log 2>&1
python3 tests/engine/retry_admission_negative.py
