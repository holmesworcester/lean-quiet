#!/usr/bin/env bash
# Each mutant breaks the codec. The laws (or Lean's termination check)
# must refuse it, so building the library fails; or, for strictness the
# laws do not state (a decoder that ignores bytes it should check is still
# sound), the check suite must fail. Runs in a scratch copy, never in this
# tree.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/mdns-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT

mutant() {  # what file old new
  local what=$1 file=$2 old=$3 new=$4
  rm -rf -- "$tmp/w"; mkdir -p "$tmp/w"
  cp -r Mdns Mdns.lean Tests tests lakefile.toml lean-toolchain "$tmp/w/"
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

mutant "a pointer may aim at itself (loops)" Mdns/Decode.lean "if p < lim then" "if p ≤ lim then"
mutant "names longer than 255 bytes" Mdns/Decode.lean "if seen + n.toNat + 2 ≤ 255 ∧" "if seen + n.toNat + 2 ≤ 256 ∧"
mutant "labels of 64 bytes (the 0x40 kind)" Mdns/Decode.lean "else if n.toNat < 64 then" "else if n.toNat < 65 then"
mutant "A records of any length" Mdns/Decode.lean "if e = i + 4 then (bytes b i 4)" "if True then (bytes b i (e - i))"
mutant "PTR rdata longer than its name" Mdns/Decode.lean "| some (n, j) => if j = e then some (.ptr n) else none" "| some (n, j) => if j ≤ e then some (.ptr n) else none"
mutant "a u16 read little-endian" Mdns/Decode.lean "pure (h * 256 + l, i)" "pure (l * 256 + h, i)"
mutant "the TTL's halves swapped" Mdns/Decode.lean "pure (h * 65536 + l, i)" "pure (l * 65536 + h, i)"
mutant "TXT strings with a short length byte" Mdns/Wire.lean "def encLabel (l : Label) : List UInt8 := l.length.toUInt8 :: l" "def encLabel (l : Label) : List UInt8 := (l.length - 1).toUInt8 :: l"
mutant "the additional section decoded as answers" Mdns/Decode.lean "answers := an, authority := au, additional := ad }" "answers := an, authority := au, additional := an }"
echo "negative controls: all killed"
