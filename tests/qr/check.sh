#!/usr/bin/env bash
# QR's deterministic gate: the laws are proven (building Qr checks them;
# tests/check.sh audits their axioms); the library has no escape hatches;
# the codec and the frame decoder pass the suite (tests/qr/Check.lean), the
# camera frames (tests/qr/camera.sh), the cross-checks against independent
# tools (tests/qr/xcheck.sh) and the negative controls.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)

lake build Qr Pic qr_check qr_tool 2>&1 | grep -E "error|✖" && exit 1

# No sorry, partial, unsafe, panic, unchecked indexing, unbounded loops or
# trusted-compiler proofs anywhere in the library.
python3 - engine/renderer/qr/*.lean engine/renderer/pic/*.lean <<'PY'
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
echo "scan: no sorry, partial, unsafe, panic, !-indexing, while/repeat, native_decide in engine/renderer/qr and engine/renderer/pic"

tests/qr/camera.sh
.lake/build/bin/qr_check out/camera/manifest.tsv
tests/qr/xcheck.sh
tests/qr/negative_controls.sh
