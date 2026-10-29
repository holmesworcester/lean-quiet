#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export CARGO_NET_OFFLINE=true
tmp=$(mktemp -d "${TMPDIR:-/tmp}/stateless-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp" engine/core engine/wire ops/sync ops/community tests/engine
python3 tests/engine/stateless_negative.py "$tmp" "$PWD/out/stateless-negative"
