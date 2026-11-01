#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/reserved-retry
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.wire.OutboxLaws reserved_retry >out/reserved-retry/build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/vacuity/RetryReservation.lean >out/reserved-retry/kernel-witness.log 2>&1
python3 tests/engine/reserved_retry_negative.py
