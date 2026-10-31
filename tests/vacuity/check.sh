#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
lake build engine.renderer.pic.Laws
audit=$(lake env lean tests/vacuity/Pictures.lean 2>&1) || { echo "$audit"; exit 1; }
echo "$audit"
AUDIT="$audit" python3 - <<'PYTHON'
import os, re
text = os.environ['AUDIT']
reports = re.findall(r"depends on axioms: \[(.*?)\]|does not depend on any axioms", text)
assert len(reports) == 5, f'Expected five axiom reports: {text}'
for report in reports:
    assert set(report.replace(' ', '').split(',')) - {''} <= {'propext', 'Classical.choice', 'Quot.sound'}, report
PYTHON
python3 tests/vacuity/controls.py
python3 tests/vacuity/inventory_test.py
python3 ci/vacuity.py
