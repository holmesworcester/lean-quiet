#!/usr/bin/env bash
# The n-node World's negative controls (tests/engine/negative_controls.py):
# each mutates the running code on a scratch snapshot and must be refused
# inside its World law. `negative_controls.sh [name...]` runs some.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/world-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp" engine/core engine/wire ops/sync engine/world
python3 tests/engine/negative_controls.py "$tmp" "$PWD/out/world-negative" "$@"
