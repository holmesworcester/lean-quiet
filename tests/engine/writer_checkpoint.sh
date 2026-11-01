#!/usr/bin/env bash
# Actual checkpoint failure/write service and a compiling recursive control.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/writer-checkpoint/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/writer-checkpoint.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app tests/engine
python3 tests/engine/writer_checkpoint_negative.py "$work" "$PWD/out/writer-checkpoint/negative"
