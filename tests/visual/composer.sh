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
.lake/build/bin/visual out/visual/composer-actual tests/visual/composer-cases.tsv
python3 tests/visual/compare.py tests/visual/composer-reference out/visual/composer-actual out/visual/composer-report --budgets tests/visual/composer-budgets.json
python3 tests/visual/check_composer_gate.py
