#!/usr/bin/env bash
# mDNS's deterministic gate: the laws are proven (building Mdns checks
# them; tests/check.sh audits their axioms), the decoder has no escape
# hatches, and the codec and service logic pass on real, hostile and
# fuzzed packets (tests/mdns/Check.lean).
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)

lake build Mdns mdns_check mdns_demo 2>&1 | grep -E "error|✖" && exit 1

# No sorry, partial, panic, unchecked indexing or trusted-compiler proof in
# the codec and its laws.
python3 - engine/wire/mdns/Wire.lean engine/wire/mdns/Decode.lean engine/wire/mdns/Laws.lean <<'PY'
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
tests/mdns/negative_controls.sh
