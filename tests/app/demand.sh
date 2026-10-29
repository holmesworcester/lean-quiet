#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/component-demand
lake build component_demand op_components scrolling
.lake/build/bin/component_demand
.lake/build/bin/op_components out/component-demand/components
# Fix the pool size for the deliberately occupied-pool regression.
LEAN_NUM_THREADS=2 .lake/build/bin/scrolling out/component-demand/scrolling backlog
python3 tests/app/scroll_report.py out/component-demand/scrolling/frames.csv --check
