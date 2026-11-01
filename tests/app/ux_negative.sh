#!/usr/bin/env bash
# ux's negative controls: each mutant breaks one dogfood fix (or the law
# beside it), and its law or the ux suite must then fail, for that
# reason. Each mutant runs in a scratch copy of its own, never in this
# tree, UX_NC_JOBS (6) at once; the unmutated copy must pass first, on
# both scroll seams.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
logs="$PWD/out/ux-negative"
mkdir -p "$logs"
# Skip controls already verified by a longer gate run; every invocation
# still builds and checks the unmodified fixture on both scroll seams.
start=${UX_NEGATIVE_START:-0}
[[ "$start" =~ ^([0-9]|10)$ ]] || { echo "UX_NEGATIVE_START must be 0..10"; exit 1; }
index=0
ran=0
label=baseline
selected() { index=$((index + 1)); (( index > start )); }
tmp=$(mktemp -d "${TMPDIR:-/tmp}/ux-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/sync engine/renderer app platforms/headless Quiet.lean assets
# The copy a control works in is $w (the caller's), its logs beside it.
build() {  # build ux in $w; 0 when it builds
  local code=0
  (cd "$w" && lake build ux >"$w.build.log" 2>&1) || code=$?
  cp "$w.build.log" "$logs/$label-build.log"
  return "$code"
}
run() {  # run ux in $w on a seam ("" or queued); its exit code
  local code=0
  (cd "$w" && .lake/build/bin/ux "$w.out" "$1" >"$w.run.log" 2>&1) || code=$?
  cp "$w.run.log" "$logs/$label-${1:-immediate}.log"
  return "$code"
}
w=$tmp/base
build || { echo "FAIL: the copy does not build"; tail -20 "$w.build.log"; exit 1; }
for seam in "" queued; do
  run "$seam" || { echo "FAIL: the unmutated copy fails ux ${seam:-immediate}"; grep -v '^slow frame' "$w.run.log"; exit 1; }
done

mutate() {  # file old new, in a fresh copy ($w)
  rm -rf -- "$w"
  cp -a "$tmp/base" "$w"
  python3 - "$w/$1" "$2" "$3" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
}
# Each control in the background, in its own copy, at most UX_NC_JOBS at once.
spawn() {  # function args...
  ran=$((ran + 1))
  while [ "$(jobs -rp | wc -l)" -ge "${UX_NC_JOBS:-6}" ]; do wait -n || true; done
  (label="control-$index"; w=$tmp/w.$index; "$@"; rm -rf -- "$w") > "$tmp/m.$(printf %03d $index).log" 2>&1 &
}
law() { selected || return 0; spawn law_one "$@"; }
suite() { selected || return 0; spawn suite_one "$@"; }
law_one() {  # what file old new: the law beside the code must refuse it
  mutate "$2" "$3" "$4"
  if build; then echo "FAIL: mutant survived its law: $1"; exit 1; fi
  grep -q "error:" "$w.build.log" || { echo "FAIL: mutant $1 failed for another reason"; tail -20 "$w.build.log"; exit 1; }
  echo "refused by its law: $1"
}
suite_one() {  # what seam expected file old new: ux must fail its check
  local what=$1 seam=$2 expected=$3
  mutate "$4" "$5" "$6"
  build || { echo "FAIL: mutant $what does not build"; tail -20 "$w.build.log"; exit 1; }
  local status=0
  run "$seam" || status=$?
  [ "$status" -eq 1 ] || { echo "FAIL: mutant $what exited $status instead of an assertion failure"; exit 1; }
  if grep -qiE 'panic|uncaught exception|segmentation fault|assertion violation' "$w.run.log"; then
    echo "FAIL: mutant $what crashed instead of failing its assertion"; exit 1
  fi
  grep -qF "FAIL $expected" "$w.run.log" ||
    { echo "FAIL: mutant $what failed for another reason"; grep -v '^slow frame' "$w.run.log"; exit 1; }
  echo "refused by ux: $what"
}

law "copy appends to the label" engine/renderer/Label.lean \
  "def copied (text : String) : String := text" "def copied (text : String) : String := text ++ \"?\""
law "each label page starts a line late" engine/renderer/Label.lean \
  "ls.extract (page * count)" "ls.extract (page * count + 1)"
law "the window may be the newest away from it" app/Screen.lean \
  "  else if near || cur.isNone then" "  else if near then"
suite "a session dot on home's avatars" "" "home avatars have no connection dots" app/community/Screen.lean \
  "    let initial := oneLine font (px 24) (String.ofList [(name.toList.headD '?').toUpper])" \
  "    b := b.round (px 38) (y + px 30) (px 46) (y + px 38) (px 4) 0x2EB67D
    let initial := oneLine font (px 24) (String.ofList [(name.toList.headD '?').toUpper])"
suite "the header's long press opens nothing" "" "long press on the header opens its complete label" app/Screen.lean \
  "| .header => pure (if s.page == .home || s.page == .chat then some s.me.name else none)" "| .header => pure none"
suite "a page row's long press opens nothing" "" "switcher long press discloses without switching" app/Screen.lean \
  "pure (Pages.fullLabel (pg.hit x (vh - 1 - y))" "pure (Pages.fullLabel Pages.Act.none"
# the window's old rule: "the newest" until an edge comes near
suite "the window stays the newest away from it" "" "a burst larger than the reader's window" app/Screen.lean \
  "let next := Lifecycle.follow s.anchor s.newer (bv ≤ 4) near" \
  "let next := if s.newer == 0 && lo ≤ winLo then none else if !near then s.anchor else Lifecycle.follow s.anchor s.newer (bv ≤ 4) near"
suite "the shift is clamped to the old range" "" "pending burst preserves the visible anchor in App.b and native Sim.b on its first frame" app/Screen.lean \
  "let cur ← s.io.scroll (bottoms s).2.toUInt32 (geom s).viewNow.toUInt32" "let cur := b.toFloat"
suite "the frame keeps no anchor" "" "pending arrival keeps the visible row at the same pixel" app/Screen.lean \
  "  if let some e := s.ownSends.head then
    anchor := some (e.message.2, presentationOffset s e.message.2)
  if b > 4 || s.restoreAnchor || s.ownSends.head.isSome then" \
  "  if let some e := s.ownSends.head then
    anchor := some (e.message.2, presentationOffset s e.message.2)
  if false then"
# a shell that shifts at vsync: the frame must paint at the shifted offset
suite "the frame paints the offset before its shift lands" queued "pending arrival keeps the visible row at the same pixel" app/Screen.lean \
  "          b := b'" "          b := (← s.io.scroll (bottoms s).2.toUInt32 (geom s).viewNow.toUInt32).toInt64.toInt.toNat"
suite "the anchor clump collapses before its new coordinate is known" "" "pending burst preserves the visible anchor" app/Screen.lean \
  "    let near := Raster.near bottom span offset viewport (over + viewport) || heldRoot == some root.2" \
  "    let near := Raster.near bottom span offset viewport (over + viewport)"
wait
[ "$ran" = 0 ] || cat "$tmp"/m.*.log
if [ "$ran" -gt 0 ] && grep -q '^FAIL' "$tmp"/m.*.log; then exit 1; fi
[ "$( (cat "$tmp"/m.*.log 2>/dev/null || true) | grep -c '^refused by')" = "$ran" ] ||
  { echo "FAIL: $ran controls, not all reported refused"; exit 1; }
echo "ux negative controls: $ran selected controls refused, each in its own copy; logs in $logs"
