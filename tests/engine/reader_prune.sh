#!/usr/bin/env bash
# Actual reader rollback, journal pruning, and strict early-ack control.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/reader-prune/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/reader-prune.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app tests/engine
python3 tests/engine/reader_prune_negative.py "$work" "$PWD/out/reader-prune/negative"
