#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
group=${1:?people or tree}
tmp=$(mktemp -d "${TMPDIR:-/tmp}/port-negative.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp" engine/core engine/wire engine/renderer ops/sync ops/community ops/connection ops/app tests/engine tests/app
python3 tests/engine/port_negative.py "$tmp" "$PWD/out/$group-negative" "$group"
