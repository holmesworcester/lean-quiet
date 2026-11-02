#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export CARGO_NET_OFFLINE=true
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build simplify live_rounds
.lake/build/bin/simplify
.lake/build/bin/live_rounds
tests/engine/simplify_negative.sh
