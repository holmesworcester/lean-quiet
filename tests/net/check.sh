#!/usr/bin/env bash
# The bootstrap's gate: build every proof (tests/check.sh audits their
# axioms); refuse sorry and added axioms in the model; run the scene on
# the real engine (Ed25519, SHA-256, SQLite); then the negative controls.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build Net
python3 - <<'PY'
import re, glob, sys
bad = []
for p in sorted(glob.glob("ops/connection/bootstrap/*.lean")):
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
tests/net/negative_controls.sh
