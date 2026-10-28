#!/usr/bin/env bash
# Each mutant breaks the codec. The laws (or Lean's termination check)
# must refuse it, so building the library fails; or, for strictness the
# laws do not state (a decoder that ignores bytes it should check is still
# sound), the check suite must fail. Runs in a scratch copy, never in this
# tree.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/mdns-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
# what every mutant starts from (tests/snapshot.sh): mDNS's sources and
# tests, and their part of the built tree
. tests/snapshot.sh
snapshot "$tmp/base" engine/wire/mdns tests/mdns
# the copy itself must build and pass, or every mutant would look killed
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build Mdns mdns_check >/dev/null 2>&1 && .lake/build/bin/mdns_check >/dev/null 2>&1) ||
  { echo "FAIL: the unmutated copy does not build and pass"; exit 1; }

mutant() {  # what file old new
  local what=$1 file=$2 old=$3 new=$4
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/$file" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
  if ! (cd "$tmp/w" && lake build Mdns >/dev/null 2>&1); then
    echo "killed by the proofs: $what"
  elif ! (cd "$tmp/w" && lake build mdns_check >/dev/null 2>&1 && .lake/build/bin/mdns_check >/dev/null 2>&1); then
    echo "killed by the checks: $what"
  else
    echo "FAIL: mutant survived: $what"; exit 1
  fi
}

mutant "a pointer may aim at itself (loops)" engine/wire/mdns/Decode.lean "if p < lim then" "if p ≤ lim then"
mutant "names longer than 255 bytes" engine/wire/mdns/Decode.lean "if seen + n.toNat + 2 ≤ 255 ∧" "if seen + n.toNat + 2 ≤ 256 ∧"
mutant "labels of 64 bytes (the 0x40 kind)" engine/wire/mdns/Decode.lean "else if n.toNat < 64 then" "else if n.toNat < 65 then"
mutant "A records of any length" engine/wire/mdns/Decode.lean "if e = i + 4 then (bytes b i 4)" "if True then (bytes b i (e - i))"
mutant "PTR rdata longer than its name" engine/wire/mdns/Decode.lean "| some (n, j) => if j = e then some (.ptr n) else none" "| some (n, j) => if j ≤ e then some (.ptr n) else none"
mutant "a u16 read little-endian" engine/wire/mdns/Decode.lean "pure (h * 256 + l, i)" "pure (l * 256 + h, i)"
mutant "the TTL's halves swapped" engine/wire/mdns/Decode.lean "pure (h * 65536 + l, i)" "pure (l * 65536 + h, i)"
mutant "TXT strings with a short length byte" engine/wire/mdns/Wire.lean "def encLabel (l : Label) : List UInt8 := l.length.toUInt8 :: l" "def encLabel (l : Label) : List UInt8 := (l.length - 1).toUInt8 :: l"
mutant "the additional section decoded as answers" engine/wire/mdns/Decode.lean "answers := an, authority := au, additional := ad }" "answers := an, authority := au, additional := an }"
echo "negative controls: all killed"
