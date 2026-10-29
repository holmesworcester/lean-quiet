#!/usr/bin/env bash
# Mutate a scratch snapshot, never the working sources. Verify the clean
# snapshot first; each control must fail its law or the TCP test.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export CARGO_NET_OFFLINE=true
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fresh-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp" engine/core engine/wire ops/sync tests/engine
python3 tests/engine/fresh_negative.py "$tmp" "$PWD/out/fresh-negative"
