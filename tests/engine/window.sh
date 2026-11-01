#!/usr/bin/env bash
# Windows and order (docs/SYNC.md, "Windows and order"): a fresh node
# gets structure first, then the newest messages and their photos
# (`newest`, also among the gate's engine suites); then the negative
# controls in a scratch snapshot (window_negative.sh).
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build app.community.channel.message.attachment.Proofs engine.sync.NewestLaws engine.sync.WindowLaws newest window_sync
.lake/build/bin/newest
.lake/build/bin/window_sync
tests/engine/window_negative.sh
