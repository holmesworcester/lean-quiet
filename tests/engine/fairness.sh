#!/usr/bin/env bash
# The umbrella's certificate stage is also runnable on its own for diagnosis.
# Bootstrap native prerequisites are supplied by the Mise crypto dependency.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/fairness
lake build vacuity_production_bootstrap vacuity_bootstrap >out/fairness/build.log 2>&1
python3 tests/engine/fairness.py
