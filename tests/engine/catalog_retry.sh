#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/catalog-retry
build=(systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0
  lake build ops.sync.SweepLaws ops.sync.SweepRun catalog_retry)
# A whole CI gate may already own this lock. Reacquiring it in a child
# would deadlock the task that is intended to check progress.
if [ "${QUIET_BUILD_LOCK_HELD:-0}" = 1 ]; then
  "${build[@]}" >out/catalog-retry/build.log 2>&1
else
  flock "$TMPDIR/lean-quiet-contracts-build.lock" "${build[@]}" >out/catalog-retry/build.log 2>&1
fi
python3 tests/engine/catalog_retry_negative.py
