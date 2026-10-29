#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
python3 -c 'import PIL, numpy'  # documented host prerequisites
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mise run crypto
lake build visual
python3 tests/visual/test_compare.py
.lake/build/bin/visual out/visual/actual tests/visual/cases.tsv
python3 tests/visual/compare.py tests/visual/reference out/visual/actual out/visual/report --budgets tests/visual/budgets.json
