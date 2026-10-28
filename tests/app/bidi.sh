#!/usr/bin/env bash
# Unicode conformance and issue regressions, built from the running renderer.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build bidi_check
.lake/build/bin/bidi_check
