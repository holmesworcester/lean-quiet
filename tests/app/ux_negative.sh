#!/usr/bin/env bash
# ux's negative controls: each mutant breaks one dogfood fix (or the law
# beside it), and its law or the ux suite must then fail, for that
# reason. Runs in a scratch copy, never in this tree; the copy must pass
# first, on both scroll seams.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/ux-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/renderer ops platforms/headless App.lean AppTypes.lean AppLife.lean Quiet.lean assets
build() {  # build ux in $tmp/w; 0 when it builds
  (cd "$tmp/w" && lake build ux >"$tmp/build.log" 2>&1)
}
run() {  # run ux in $tmp/w on a seam ("" or queued); its exit code
  (cd "$tmp/w" && .lake/build/bin/ux "$tmp/out" $1 >"$tmp/run.log" 2>&1)
}
cp -a "$tmp/base" "$tmp/w"
build || { echo "FAIL: the copy does not build"; tail -20 "$tmp/build.log"; exit 1; }
for seam in "" queued; do
  run "$seam" || { echo "FAIL: the unmutated copy fails ux ${seam:-immediate}"; grep -v '^slow frame' "$tmp/run.log"; exit 1; }
done

mutate() {  # file old new, in a fresh copy
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/$1" "$2" "$3" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
}
law() {  # what file old new: the law beside the code must refuse it
  mutate "$2" "$3" "$4"
  if build; then echo "FAIL: mutant survived its law: $1"; exit 1; fi
  grep -q "error:" "$tmp/build.log" || { echo "FAIL: mutant $1 failed for another reason"; tail -20 "$tmp/build.log"; exit 1; }
  echo "refused by its law: $1"
}
suite() {  # what seam expected file old new: ux must fail its check
  local what=$1 seam=$2 expected=$3
  mutate "$4" "$5" "$6"
  build || { echo "FAIL: mutant $what does not build"; tail -20 "$tmp/build.log"; exit 1; }
  if run "$seam"; then echo "FAIL: mutant survived ux: $what"; exit 1; fi
  grep -q "FAIL $expected" "$tmp/run.log" ||
    { echo "FAIL: mutant $what failed for another reason"; grep -v '^slow frame' "$tmp/run.log"; exit 1; }
  echo "refused by ux: $what"
}

law "copy appends to the label" engine/renderer/Label.lean \
  "def copied (text : String) : String := text" "def copied (text : String) : String := text ++ \"?\""
law "each label page starts a line late" engine/renderer/Label.lean \
  "ls.extract (page * count)" "ls.extract (page * count + 1)"
law "the window may be the newest away from it" ops/app/Lifecycle.lean \
  "  else if near || cur.isNone then" "  else if near then"
suite "a session dot on home's avatars" "" "home avatars have no connection dots" ops/app/Pages.lean \
  "    let ini := String.ofList [(n.toList.headD '?').toUpper]" \
  "    let r := dm.px 6
    let cx := dm.px 48
    let cy := y + (rh + d) / 2
    b := b.round (cx - r) (cy - r) (cx + r) (cy + r) r 0x2EB67D
    let ini := String.ofList [(n.toList.headD '?').toUpper]"
suite "the header's long press opens nothing" "" "long press on the header opens its complete label" App.lean \
  "| .header => pure (if s.page == .home || s.page == .chat then some s.me.name else none)" "| .header => pure none"
suite "a page row's long press opens nothing" "" "switcher long press discloses without switching" App.lean \
  "pure (Pages.fullLabel (pg.hit x (vh - 1 - y))" "pure (Pages.fullLabel Pages.Act.none"
# the window's old rule: "the newest" until an edge comes near
suite "the window stays the newest away from it" "" "a burst larger than the reader's window" App.lean \
  "let next := Lifecycle.follow s.anchor s.newer (bv ≤ 4) near" \
  "let next := if s.newer == 0 && lo ≤ winLo then none else if !near then s.anchor else Lifecycle.follow s.anchor s.newer (bv ≤ 4) near"
suite "the shift is clamped to the old range" "" "a burst larger than the reader's window" App.lean \
  "let cur ← s.io.scroll (bottoms s).2.toUInt32 vh.toUInt32" "let cur := b.toUInt32"
suite "the frame keeps no anchor" "" "pending arrival keeps the visible row at the same pixel" App.lean \
  "  if b > 4 || s.restoreAnchor then" "  if false then"
# a shell that shifts at vsync: the frame must paint at the shifted offset
suite "the frame paints the offset before its shift lands" queued "pending arrival keeps the visible row at the same pixel" App.lean \
  "          b := b'" "          b := (← s.io.scroll (bottoms s).2.toUInt32 vh.toUInt32).toNat"
echo "ux negative controls: all refused"
