#!/usr/bin/env bash
# Remove a real invisible/blank classification in a scratch copy. The
# complete painter scan must name the omitted character, not just fail.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/inkless-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/renderer ops platforms/headless assets
logs="$PWD/out/inkless-negative"
mkdir -p "$logs"
run() {
  (cd "$tmp/w" && lake build inkless) >"$logs/build.log" 2>&1 ||
    { echo "FAIL: inkless control did not compile"; tail -20 "$logs/build.log"; exit 1; }
  (cd "$tmp/w" && .lake/build/bin/inkless) >"$logs/$1.log" 2>&1
}
cp -a "$tmp/base" "$tmp/w"
run base || { cat "$logs/base.log"; exit 1; }
mutant() {
  local file=$1 old=$2 new=$3 cp=$4
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/$file" "$old" "$new" <<'PY'
from pathlib import Path
import sys
p, old, new = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
s = p.read_text()
assert s.count(old) == 1, 'mutation must match exactly once'
p.write_text(s.replace(old, new))
PY
  if run "$cp"; then echo "FAIL: inkless control survived: $cp"; exit 1; fi
  grep -q "^FAIL inkless glyphs names cannot tell apart:.*$cp " "$logs/$cp.log" ||
    { echo "FAIL: inkless control failed for another reason"; cat "$logs/$cp.log"; exit 1; }
  echo "refused by inkless: $cp removed from $file"
}
mutant engine/renderer/Chars.lean 'inRange c 0x2066 0x2069' 'inRange c 0x2067 0x2069' U+2066
mutant ops/community/Facts.lean 'c == 0x3164 || ' '' U+3164
echo "inkless negative controls: both refused; working sources untouched"
