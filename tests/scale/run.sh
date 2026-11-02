#!/usr/bin/env bash
# The scaling test (docs/BOUNDS.md): what a round's work costs at 1k, 10k
# and 100k items in one room, on the code that runs, checked against the
# proven bounds, with each fix's negative control. Table in
# out/scale/scale.tsv (times are reported, not asserted).
#   tests/scale/run.sh [sizes...]   (default: 1000 10000 100000)
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build scale
mkdir -p out/scale
.lake/build/bin/scale out/scale "$@"
