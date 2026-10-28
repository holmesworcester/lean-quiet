#!/usr/bin/env bash
# Each mutant breaks the codec. The laws (or Lean's termination check)
# must refuse it, so building the library fails; or, for what the laws do
# not state (the matrix layout, the image pipeline, error correction's
# completeness), the check suite must fail: its frozen qrencode matrices
# catch an encoder and decoder that agree with each other but not with the
# standard. Runs in a scratch copy, never in this tree.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
root=$PWD
manifest=$root/out/camera/manifest.tsv
[ -f "$manifest" ] || tests/camera.sh >/dev/null
tmp=$(mktemp -d "${TMPDIR:-/tmp}/qr-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT

copy() {
  rm -rf -- "$tmp/w"; mkdir -p "$tmp/w"
  cp -r Qr Qr.lean Tests tests lakefile.toml lake-manifest.json lean-toolchain "$tmp/w/"
  # the built tree, so that only what the mutant touches is rebuilt
  [ -d .lake ] && cp -a .lake "$tmp/w/"
}

# the copy itself must build and pass, or every mutant would look killed
copy
(cd "$tmp/w" && lake build Qr qr_check >/dev/null 2>&1 && .lake/build/bin/qr_check "$manifest" >/dev/null 2>&1) ||
  { echo "FAIL: the unmutated copy does not build and pass"; exit 1; }

mutant() {  # what file old new
  local what=$1 file=$2 old=$3 new=$4
  copy
  python3 - "$tmp/w/$file" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
  if ! (cd "$tmp/w" && lake build Qr >"$tmp/build.log" 2>&1); then
    # a proof (or termination) must be what failed, not the code itself
    if python3 - "$tmp/w" "$tmp/build.log" <<'PY2'
import re, sys
root, log = sys.argv[1], open(sys.argv[2]).read()
errs = re.findall(r'error: ([\w/]+\.lean):(\d+):\d+: (.*)', log)
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev|instance|structure|inductive)\b')
def kind(f, line):
    lines = open(f'{root}/{f}').read().split('\n')[:int(line)]
    for l in reversed(lines):
        if re.match(r'\s*(decreasing_by|termination_by)\b', l):
            return 'termination'
        m = decl.match(l)
        if m:
            return m.group(1)
    return '?'
ok = bool(errs) and all(kind(f, l) in ('theorem', 'lemma', 'termination') or
                        re.search(r'termination|decreasing|well-founded|structural recursion', msg)
                        for f, l, msg in errs)
sys.exit(0 if ok else 1)
PY2
    then
      echo "killed by the proofs: $what"
    else
      echo "FAIL: mutant does not compile (not a proof failure): $what"; grep error "$tmp/build.log" | head -3; exit 1
    fi
  elif ! (cd "$tmp/w" && lake build qr_check >/dev/null 2>&1 && .lake/build/bin/qr_check "$manifest" >/dev/null 2>&1); then
    echo "killed by the checks: $what"
  else
    echo "FAIL: mutant survived: $what"; exit 1
  fi
}

# data stream (the laws)
mutant "bits written least significant first" Qr/Bits.lean "| k + 1 => (n / 2 ^ k % 2 == 1) :: bitsOf n k" "| k + 1 => (n / 2 ^ k % 2 == 1) :: bitsOf (n / 2) k"
mutant "three digits up to 1023 accepted" Qr/Segment.lean "if x < 1000 then" "if x < 1024 then"
mutant "alphanumeric pairs up to 2047 accepted" Qr/Segment.lean "if x < 2025 then" "if x < 2048 then"
mutant "a byte read off by one" Qr/Segment.lean "| some (cs, r) => some (x.toUInt8 :: cs, r)" "| some (cs, r) => some ((x + 1).toUInt8 :: cs, r)"
mutant "ECI numbers of 21 bits unchecked" Qr/Segment.lean "if x < 1000000 then some (x, r) else none" "some (x, r)"
mutant "parse recurses without consuming" Qr/Segment.lean "| some (s, r') => (parse v r').map (s :: ·)" "| some (s, r') => (parse v (r' ++ bs)).map (s :: ·)"
mutant "terminator not written" Qr/Segment.lean "let t := bs ++ List.replicate (min 4 (8 * cap - bs.length)) false" "let t := bs"
# format and version information, Reed–Solomon (the laws)
mutant "format readings 4 bits off accepted" Qr/Format.lean "(List.range 32).find? fun d => hd 15 (bchFormat d) x ≤ 3" "(List.range 32).find? fun d => hd 15 (bchFormat d) x ≤ 4"
mutant "version readings 4 bits off accepted" Qr/Format.lean "(List.range' 7 34).find? fun v => hd 18 (bchVersion v) x ≤ 3" "(List.range' 7 34).find? fun v => hd 18 (bchVersion v) x ≤ 4"
mutant "corrections beyond capacity returned" Qr/RS.lean "&& decide (dist r c ≤ k / 2) then some c" "then some c"
mutant "corrected block not re-checked" Qr/RS.lean "if allZero (syndromes k c) && c.size == r.size" "if c.size == r.size"
# what the laws do not state (the checks)
mutant "Berlekamp–Massey's length rule" Qr/RS.lean "if 2 * l ≤ i then" "if 2 * l < i then"
mutant "Forney's formula without X" Qr/RS.lean "let v := mul (exp e) (div (evalLow om xinv) den)" "let v := div (evalLow om xinv) den"
mutant "the format mask constant" Qr/Format.lean "((d <<< 10) ||| r) ^^^ 0x5412" "((d <<< 10) ||| r) ^^^ 0x1234"
mutant "mask 4's pattern" Qr/Matrix.lean "| 4 => (x / 3 + y / 2) % 2 == 0" "| 4 => (x / 2 + y / 3) % 2 == 0"
mutant "zigzag strips the wrong way" Qr/Matrix.lean "let upward := (right + 1) &&& 2 == 0" "let upward := (right + 1) &&& 2 != 0"
mutant "byte count field of 9 bits" Qr/Tables.lean "| 0 => [10, 12, 14] | 1 => [9, 11, 13] | 2 => [8, 16, 16]" "| 0 => [10, 12, 14] | 1 => [9, 11, 13] | 2 => [9, 16, 16]"
mutant "an alignment pattern step" Qr/Tables.lean "let step := if v = 32 then 26" "let step := if v = 32 then 28"
mutant "blocks interleaved in the wrong order" Qr/ReadGrid.lean "  for _ in [0:l.ecLen] do
    for b in [0:l.nb] do
      blocks := blocks.modify b" "  for _ in [0:l.ecLen] do
    for b in [0:l.nb] do
      blocks := blocks.modify (l.nb - 1 - b)"
mutant "finder triangle oriented the wrong way" Qr/Decode.lean "if cross ≥ 0 then (tl, p, q) else (tl, q, p)" "if cross ≤ 0 then (tl, p, q) else (tl, q, p)"
mutant "modules sampled at their corners" Qr/Decode.lean "let p := t.apply (x.toFloat + 0.3 + 0.2 * i.toFloat) (y.toFloat + 0.3 + 0.2 * j.toFloat)" "let p := t.apply (x.toFloat + 0.2 * i.toFloat) (y.toFloat + 0.2 * j.toFloat)"
mutant "a global threshold only" Qr/Decode.lean "else (decodeBits (hybridBits img)).orElse fun _ => decodeBits (globalBits img)" "else decodeBits (globalBits img)"
mutant "no alignment patterns" Qr/Decode.lean "  if ps.length == 0 then return t0
  let e := n.toFloat - 3.5
  let mut src" "  if true then return t0
  let e := n.toFloat - 3.5
  let mut src"
echo "negative controls: all killed"
