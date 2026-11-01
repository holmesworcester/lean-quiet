#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/catalog-retry
flock /mnt/storage/holmes-tmp/lean-quiet-contracts-build.lock \
  systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build ops.sync.SweepLaws ops.sync.SweepRun catalog_retry >out/catalog-retry/build.log 2>&1
python3 tests/engine/catalog_retry_negative.py
