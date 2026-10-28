#!/usr/bin/env bash
# pic_retry's negative controls: each mutant takes away half of what lets
# a picture whose chunks land while its retry waits show at once, and
# pic_retry must then fail (the decode waits out its two seconds). Runs
# in a scratch copy, never in this tree; the copy must pass first.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/pic-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/renderer ops platforms/headless App.lean Quiet.lean assets
run() {  # build and run pic_retry in $tmp/w; its exit code
  (cd "$tmp/w" && lake build pic_retry >"$tmp/build.log" 2>&1) || { echo "FAIL: the copy does not build"; tail -20 "$tmp/build.log"; exit 1; }
  (cd "$tmp/w" && .lake/build/bin/pic_retry "$tmp/out" >"$tmp/run.log" 2>&1)
}
cp -a "$tmp/base" "$tmp/w"
run || { echo "FAIL: the unmutated copy fails pic_retry"; grep -v '^slow frame' "$tmp/run.log"; exit 1; }

mutant() {  # what old new (in App.lean)
  local what=$1 old=$2 new=$3
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/App.lean" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
  if run; then echo "FAIL: mutant survived: $what"; exit 1; fi
  grep -q "FAIL its file's decode starts within a few frames" "$tmp/run.log" ||
    { echo "FAIL: mutant $what failed for another reason"; grep -v '^slow frame' "$tmp/run.log"; exit 1; }
  echo "refused by pic_retry: $what"
}

# the want lapses with the frame that asked: a waiting key's chunks are
# never read, so its wait is never cleared
mutant "a waiting key's chunk read is not kept wanted" \
  "let pics := s.retryWants.fold (fun ws _ w => if ws.contains w then ws else ws.push w) s.picWants" \
  "let pics := s.picWants"
# the chunks are read, but the wait stands until frames + 120
mutant "the board's chunk bytes do not clear the wait" \
  "    modify fun s => { s with imgRetry := {}, retryWants := {} }" \
  "    pure ()"
echo "pic_retry negative controls: all refused"
