#!/usr/bin/env bash
# The deterministic gate: the laws are proven (building Mdns checks them),
# on Lean's standard axioms only, the decoder has no escape hatches, and
# the codec and service logic pass on real, hostile and fuzzed packets.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"

lake build Mdns mdns_check mdns_demo 2>&1 | grep -E "error|✖" && exit 1

ax=$(lake env lean tests/axioms.lean)
echo "$ax"
n=$(echo "$ax" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" || true)
[ "$n" = 3 ] || { echo "FAIL: a law depends on more than the standard axioms"; exit 1; }

# No sorry, partial, panic, unchecked indexing or trusted-compiler proof in
# the codec and its laws.
python3 - Mdns/Wire.lean Mdns/Decode.lean Mdns/Laws.lean <<'PY'
import re, sys
bad = re.compile(r'\bsorry\b|\bpartial\b|panic|\]!|get!|native_decide|bv_decide|implemented_by|@\[extern')
hit = False
for p in sys.argv[1:]:
    code = re.sub(r'/-.*?-/', '', open(p).read(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    for m in bad.finditer(code):
        print(f"{p}: forbidden {m.group(0)!r}"); hit = True
sys.exit(1 if hit else 0)
PY

.lake/build/bin/mdns_check
tests/negative_controls.sh
