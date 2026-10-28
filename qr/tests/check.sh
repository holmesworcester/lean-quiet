#!/usr/bin/env bash
# The deterministic gate: the laws are proven (building Qr checks them) on
# Lean's standard axioms only; the library has no escape hatches; the
# codec and the frame decoder pass the suite (Tests/Check.lean), the
# camera frames (tests/camera.sh), the cross-checks against independent
# tools (tests/xcheck.sh) and the negative controls.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"

lake build Qr qr_check qr_tool 2>&1 | grep -E "error|✖" && exit 1

ax=$(lake env lean tests/axioms.lean)
echo "$ax"
std='(propext|Classical.choice|Quot.sound)'
n=$(echo "$ax" | grep -cE "depends on axioms: \[$std(, $std)*\]$" || true)
[ "$n" = "$(grep -c '^#print axioms' tests/axioms.lean)" ] ||
  { echo "FAIL: a law depends on more than the standard axioms"; exit 1; }

# No sorry, partial, unsafe, panic, unchecked indexing, unbounded loops or
# trusted-compiler proofs anywhere in the library.
python3 - Qr/*.lean <<'PY'
import re, sys
bad = re.compile(r'\bsorry\b|\bpartial\b|\bunsafe\b|panic|unreachable|\]!|\w!(?![="])|'
                 r'\bwhile\b|\brepeat\b|native_decide|\+native|bv_decide|implemented_by|@\[extern')
hit = False
for p in sys.argv[1:]:
    code = re.sub(r'/-.*?-/', '', open(p).read(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    code = re.sub(r'"(\\.|[^"\\])*"', '""', code)
    for m in bad.finditer(code):
        print(f"{p}: forbidden {m.group(0)!r}"); hit = True
sys.exit(1 if hit else 0)
PY
echo "scan: no sorry, partial, unsafe, panic, !-indexing, while/repeat, native_decide in Qr/"

tests/camera.sh
.lake/build/bin/qr_check out/camera/manifest.tsv
tests/xcheck.sh
tests/negative_controls.sh
