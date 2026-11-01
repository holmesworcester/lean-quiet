#!/usr/bin/env bash
# Actual reader transaction/admission cutoff and compiling loss controls.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/reader-claim/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/reader-claim.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app tests/engine
python3 tests/engine/reader_claim_negative.py "$work" "$PWD/out/reader-claim/negative"
