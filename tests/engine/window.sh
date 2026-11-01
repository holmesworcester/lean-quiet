#!/usr/bin/env bash
# Windows and order (docs/SYNC.md, "Windows and order"): a message's
# attachment and chunks sort at its time (chunks_in_window; the vacuity
# fixture checks real ops), then the negative controls in a scratch
# snapshot (window_negative.sh).
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build app.community.channel.message.attachment.Proofs
tests/engine/window_negative.sh
