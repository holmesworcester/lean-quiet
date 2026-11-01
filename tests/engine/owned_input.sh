#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
if [ "${OWNED_INPUT_SCOPED:-0}" != 1 ]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env OWNED_INPUT_SCOPED=1 bash "$0" "$@"
fi
mkdir -p out/owned-input-core
"$ELAN_HOME/bin/lake" build +engine.renderer.Session >out/owned-input-core/prerequisite-build.log 2>&1
exec python3 tests/engine/owned_input.py
