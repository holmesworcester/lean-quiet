#!/usr/bin/env bash
# Pre-admission sessions (docs/TAKE-ROOM.md): the runtime witness (a
# removed node holding the community opens a stranger's link; the
# session takes c and sends none of it; the shipped selection serves the
# history; an honest rejoin still completes), then the mutants that
# restore the leak, each rejected inside its law. Logs: out/preadmit.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/preadmit
systemd-run --user --scope -q -p CPUWeight=1000 -p MemoryMax=16G -p MemorySwapMax=0 \
  lake build app.Proofs engine.sync.TakeLaws vacuity_identity_preadmit >out/preadmit/build.log 2>&1
.lake/build/bin/vacuity_identity_preadmit | tee out/preadmit/witness.log
grep -q 'passed, 0 failed' out/preadmit/witness.log
python3 tests/engine/preadmit_negative.py
