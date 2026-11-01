#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
if [ "${1:-}" = --list ]; then exec python3 tests/app/lifecycle_node_negative.py --list; fi
if [ "${LIFECYCLE_NODE_SCOPED:-0}" != 1 ]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env LIFECYCLE_NODE_SCOPED=1 bash "$0" "$@"
fi
# Wiring imports every library, including proof modules outside Main's closure.
# The named task must prepare them even when no earlier full CI build ran.
lake build
lake build +Main
python3 tests/app/lifecycle_node_negative.py "$@"
