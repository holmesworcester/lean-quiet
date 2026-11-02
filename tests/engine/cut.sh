#!/usr/bin/env bash
# The causal cut of removals (docs/REMOVAL.md): cut_check on SQLite, then
# its negative controls in a snapshot (cut_negative.py): each mutant of
# the trust rule's views fails its assertion and is refused by its law.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build cut_check app.community.Proofs
.lake/build/bin/cut_check out/cut
tmp=$(mktemp -d "${TMPDIR:-/tmp}/cut-negative.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp" engine/core engine/wire engine/renderer engine/sync app tests/engine tests/app
python3 tests/engine/cut_negative.py "$tmp" "$PWD/out/cut-negative"
