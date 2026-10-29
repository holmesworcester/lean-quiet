#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mise run crypto
lake build visual
.lake/build/bin/visual out/visual/hover-actual tests/visual/hover-cases.tsv
python3 tests/visual/compare_hover.py --budgets tests/visual/hover-budgets.json
python3 tests/visual/check_hover_gate.py
