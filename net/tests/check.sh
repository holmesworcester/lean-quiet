#!/usr/bin/env bash
# The gate: build every proof; require the laws to rest on Lean's
# standard axioms only; refuse sorry and added axioms in the model; run
# the scene on the real engine (Ed25519, SHA-256, SQLite); then the
# negative controls.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
lake build Net
out=$(lake env lean tests/Axioms.lean)
echo "$out"
n=$(grep -c "depends on axioms\|does not depend on any axioms" <<<"$out")
want=$(grep -c "^#print axioms" tests/Axioms.lean)
[ "$n" -eq "$want" ] || { echo "expected $want axiom reports, got $n" >&2; exit 1; }
bad=$(grep "depends on axioms" <<<"$out" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
[ -z "$bad" ] || { echo "non-standard axioms: $bad" >&2; exit 1; }
echo "all $want laws rest on standard axioms only"
python3 - <<'PY'
import re, glob, sys
bad = []
for p in sorted(glob.glob("Net/*.lean")) + ["Net.lean"]:
    s = re.sub(r"/-.*?-/", "", open(p).read(), flags=re.S)
    s = re.sub(r"--.*", "", s)
    # (an admit tactic elaborates to sorryAx, which the axiom audit refuses)
    for w in ["sorry", "native_decide", "implemented_by", "@[extern"]:
        if re.search(r"(?<![\w.])" + re.escape(w) + r"(?![\w])", s):
            bad.append(f"{p}: {w}")
    if re.search(r"^\s*axiom\s", s, flags=re.M):
        bad.append(f"{p}: axiom")
if bad:
    print("forbidden:", *bad, sep="\n  "); sys.exit(1)
print("no sorry, axiom, native_decide or extern in the model")
PY
lake build scene_check
mkdir -p out
.lake/build/bin/scene_check out/scene
tests/negative_controls.sh
