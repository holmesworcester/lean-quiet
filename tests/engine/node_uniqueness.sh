#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/node-uniqueness
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build app.Proofs +tests.vacuity.NodeUnique node_uniqueness \
  >out/node-uniqueness/named-build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/engine/NodeUniqueAxioms.lean >out/node-uniqueness/axioms.log 2>&1
python3 - <<'PY'
from pathlib import Path
import re
text = Path('out/node-uniqueness/axioms.log').read_text()
assert 'sorryAx' not in text and 'error:' not in text, text
reports = re.findall(r'depends on axioms: \[(.*?)\]|does not depend on any axioms', text, re.S)
assert len(reports) == 11, (len(reports), text)
for report in reports:
    assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', report)) <= {'propext', 'Classical.choice', 'Quot.sound'}, report
print('11 Node uniqueness laws use standard axioms only')
PY
python3 tests/engine/node_uniqueness_negative.py
