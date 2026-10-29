#!/usr/bin/env bash
# T-fresh: a fresh post's latency while a backlog of N chunks syncs, in
# simulated time, against the old order (fresh); over real TCP, a peer
# that never reads stops no one else (fresh_tcp); then the negative
# controls (fresh_negative.sh). docs/SYNC.md, "Lanes".
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build fresh fresh_tcp
.lake/build/bin/fresh ${FRESH_N:-}
if [ "${SKIP_TCP:-0}" != 1 ]; then
  .lake/build/bin/fresh_tcp
  tests/engine/fresh_negative.sh
else
  echo "SKIP fresh_tcp and its negative controls (TCP sandbox; built)"
fi
