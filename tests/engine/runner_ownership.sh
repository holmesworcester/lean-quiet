#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/runner-ownership
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.wire.JobOwnersLaws runner_ownership >out/runner-ownership/build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/vacuity/JobOwners.lean >out/runner-ownership/kernel-witness.log 2>&1
python3 tests/engine/runner_ownership_negative.py
