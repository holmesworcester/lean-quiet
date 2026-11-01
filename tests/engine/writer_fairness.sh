#!/usr/bin/env bash
# Real writer loop/SQLite fairness, exact production queue laws and controls.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/writer-fairness
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.renderer.WriteQueueLaws engine.wire.PriorityLaws engine.wire.LaneLaws \
    +tests.vacuity.WriterFairness writer_fairness \
  >out/writer-fairness/build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/engine/WriterFairnessAxioms.lean >out/writer-fairness/axioms.log 2>&1
python3 tests/engine/writer_fairness_negative.py
