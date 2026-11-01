#!/usr/bin/env bash
# make install's assets step (tools/make/assets.sh, tools/make/assets.py)
# on small made-up tarballs served by file://, with negative controls:
# a corrupted download, a tarball whose files don't match the list, plain
# http and an unreachable URL are each rejected and leave assets/ as it
# was; packing ignores times, owners and modes; the pin check fails on a
# stale list and on changed asset scripts. With the pinned tarball in
# out/make (tools/make/assets.py pack), it also unpacks that one.
# No network. Logs: out/make/assets-test/.
set -euo pipefail
top=$(cd "$(dirname "$0")/../.." && pwd)
logs=$top/out/make/assets-test
rm -rf "$logs"; mkdir -p "$logs"
w=$(mktemp -d "${TMPDIR:-/tmp}/lq-assets-test.XXXXXX")
trap 'rm -rf "$w"' EXIT
pass=0
ok() { pass=$((pass + 1)); echo "ok  $*"; }
fail() { echo "FAIL $*" >&2; echo "logs: $logs" >&2; exit 1; }
# assets.sh against the made-up pin and list, into $w/dest
fetch() {
  local name=$1 url=$2
  LQ_ASSETS_URL=$url LQ_ASSETS_DIR=$w/dest LQ_ASSETS_PIN=$w/pin LQ_ASSETS_MANIFEST=$w/list \
    LQ_ASSETS_FALLBACK=0 "$top/tools/make/assets.sh" > "$logs/$name.log" 2>&1
}
same_dir() { diff -r "$1" "$2" > /dev/null; }

mkdir -p "$w/src" "$w/out"
printf 'Ελληνικά 日本語\n' > "$w/src/a.txt"
head -c 70000 /dev/urandom > "$w/src/b.bin"
python3 "$top/tools/make/assets.py" pack --assets "$w/src" --out "$w/out" --manifest "$w/list" --pin "$w/pin" > "$logs/pack.log"
. "$w/pin"
tarball=$w/out/$LQ_ASSETS_NAME
[ -f "$tarball" ] || fail "pack wrote no $LQ_ASSETS_NAME"

# Packing again after changing times, modes and the order files were made
# gives the same bytes.
cp "$tarball" "$w/first.tar.gz"
touch -d '2001-02-03' "$w/src/a.txt"; chmod 600 "$w/src/b.bin"
python3 "$top/tools/make/assets.py" pack --assets "$w/src" --out "$w/out" --manifest "$w/list2" --pin "$w/pin2" > "$logs/pack-again.log"
cmp -s "$w/first.tar.gz" "$tarball" || fail "packing the same files twice gave different bytes"
ok "pack: same files, same bytes (times, modes ignored)"
TZ=UTC tar -tvzf "$tarball" > "$logs/listing.txt"
grep -q ' 0/0 ' "$logs/listing.txt" && ! grep -qv '1970-01-01' "$logs/listing.txt" || fail "tar entries carry owners or times"
ok "pack: owner 0/0, time 0 on every entry"

fetch good "file://$tarball" || fail "a good tarball was refused"
same_dir "$w/src" "$w/dest" || fail "the unpacked files differ from the packed ones"
ok "a good tarball unpacks into assets/"

fetch in-place "file://$w/nothing-here.tar.gz" || fail "complete assets/ still needed a download"
grep -q 'in place' "$logs/in-place.log" || fail "complete assets/ was not recognised"
ok "complete assets/: no download"

printf 'damaged' > "$w/dest/a.txt"
fetch repair "file://$tarball" || fail "a damaged assets/ was not repaired"
same_dir "$w/src" "$w/dest" || fail "the repaired assets/ differs"
ok "a damaged file in assets/ is replaced"

# Negative controls: each leaves no assets/ behind.
python3 - "$tarball" "$w/corrupt.tar.gz" <<'EOF'
import sys
data = bytearray(open(sys.argv[1], 'rb').read())
data[len(data) // 2] ^= 0x01
open(sys.argv[2], 'wb').write(data)
EOF
rm -rf "$w/dest"
if fetch corrupt "file://$w/corrupt.tar.gz"; then fail "a corrupted tarball was accepted"; fi
grep -q "rejected.*sha256 is" "$logs/corrupt.log" || fail "the corrupted tarball's rejection does not name the sha256"
[ ! -e "$w/dest" ] || fail "a corrupted tarball left files in assets/"
ok "control: a tarball with one flipped bit is rejected before unpacking"

cp "$w/list" "$w/list.good"
sed -i '1s/^./0/; 1s/^00/11/' "$w/list"
if fetch stale-list "file://$tarball"; then fail "files not matching the list were accepted"; fi
grep -q "don't match" "$logs/stale-list.log" || fail "the list mismatch was not reported"
[ ! -e "$w/dest" ] || fail "a list mismatch left files in assets/"
cp "$w/list.good" "$w/list"
ok "control: a tarball whose files don't match the list is rejected"

if fetch http "http://127.0.0.1:9/$LQ_ASSETS_NAME"; then fail "plain http was used"; fi
[ ! -e "$w/dest" ] || fail "plain http left files in assets/"
ok "control: plain http is refused"

if fetch missing "file://$w/nothing-here.tar.gz"; then fail "a missing tarball passed"; fi
grep -q 'could not download' "$logs/missing.log" || fail "the missing download was not reported"
ok "control: an unreachable tarball fails (fallback off)"

# The real pin against this tree, and two stale copies of it.
python3 "$top/tools/make/assets.py" check > "$logs/pin.log" 2>&1 || fail "tools/make/assets.sha256 is stale: $(tail -3 "$logs/pin.log")"
ok "pin: tools/make/assets.sha256 matches this tree's asset hashes and stamps"
# a list whose Noto font, then whose glyph stamp, is not this tree's
for entry in NotoSans-Regular.ttf ui-glyphs.sha256; do
  awk -v e="$entry" '$2 == e { $1 = "0000000000000000000000000000000000000000000000000000000000000000" } { print $1 "  " $2 }' \
    "$top/tools/make/assets.sha256" > "$w/stale.sha256"
  if python3 "$top/tools/make/assets.py" check --manifest "$w/stale.sha256" > "$logs/pin-stale-$entry.log" 2>&1; then
    fail "a file list with a stale $entry passed the pin check"
  fi
  grep -q "^stale: $entry:" "$logs/pin-stale-$entry.log" || fail "the stale $entry was not named"
done
ok "control: a stale font hash or glyph stamp fails the pin check"
sed 's/^LQ_ASSETS_MAKERS=.*/LQ_ASSETS_MAKERS=0/' "$top/tools/make/assets.pin" > "$w/stale.pin"
if python3 "$top/tools/make/assets.py" check --pin "$w/stale.pin" > "$logs/pin-makers.log" 2>&1; then
  fail "changed asset scripts passed the pin check"
fi
grep -q 'changed since the tarball was packed' "$logs/pin-makers.log" || fail "the changed scripts were not named"
ok "control: changed asset scripts fail the pin check"

. "$top/tools/make/assets.pin"
if [ -f "$top/out/make/$LQ_ASSETS_NAME" ]; then
  rm -rf "$w/real"
  LQ_ASSETS_URL="file://$top/out/make/$LQ_ASSETS_NAME" LQ_ASSETS_DIR=$w/real LQ_ASSETS_FALLBACK=0 \
    "$top/tools/make/assets.sh" > "$logs/real.log" 2>&1 || fail "the pinned tarball was refused: $(tail -2 "$logs/real.log")"
  [ "$(ls "$w/real" | wc -l)" = "$(wc -l < "$top/tools/make/assets.sha256")" ] || fail "the pinned tarball unpacked the wrong files"
  ok "the pinned tarball ($LQ_ASSETS_NAME) unpacks and checks"
else
  echo "skip the pinned tarball: no out/make/$LQ_ASSETS_NAME (tools/make/assets.py pack)"
fi
echo "assets: $pass checks passed"
