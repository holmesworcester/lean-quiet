#!/usr/bin/env bash
# The umbrella's certificate stage is also runnable on its own for diagnosis.
# Bootstrap native prerequisites are supplied by the Mise crypto dependency.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/fairness
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 lake build vacuity_production_bootstrap vacuity_connection_progress vacuity_closure_delivery vacuity_round_exchange vacuity_storage_effects >out/fairness/build.log 2>&1
python3 tests/engine/fairness.py
