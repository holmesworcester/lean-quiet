#!/usr/bin/env bash
# Deterministic zoom gate: build/setup, proofs, real glyph/layout and X11 tests.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p out/zoom
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mise run crypto
lake build linux visual zoom engine.renderer.desktop.ZoomLaws engine.renderer.WrapLaws engine.renderer.TextLaws
lake env lean tests/zoom/Axioms.lean > out/zoom/axioms.log
python3 - <<'PY'
import re
s=open('out/zoom/axioms.log').read()
assert len(s.splitlines())==11,s
for group in re.findall(r'depends on axioms: \[([^]]*)\]',s):
    assert set(group.split(', ')) <= {'propext','Classical.choice','Quot.sound'},group
PY
.lake/build/bin/zoom | tee out/zoom/geometry.log
platforms/linux/input_test.sh > out/zoom/input.log 2>&1
python3 tests/zoom/native.py > out/zoom/native.log 2>&1
.lake/build/bin/visual out/zoom/actual tests/zoom/cases.tsv > out/zoom/capture.log
python3 tests/zoom/geometry.py
python3 tests/visual/compare.py tests/zoom/reference out/zoom/actual out/zoom/report --budgets tests/zoom/budgets.json > out/zoom/compare.log
