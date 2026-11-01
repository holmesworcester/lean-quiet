#!/usr/bin/env bash
# A joiner's scene on the real engine (Ed25519, SHA-256, SQLite): the
# running trust rule and validators over every subset of its five ops;
# then the negative controls, mutants of that running code that the
# proofs must refuse. (The bootstrap model these once checked is retired:
# its laws were over a protocol nothing runs.)
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build +app.community.Proofs +app.Proofs
lake build scene_check
mkdir -p out
.lake/build/bin/scene_check out/scene
tests/net/negative_controls.sh
