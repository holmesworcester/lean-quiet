#!/usr/bin/env bash
# busy_runner's negative controls, each in a scratch snapshot, never the
# working sources. busy_runner passes on the running code; each mutant
# puts back one way a busy store used to stop the runner, and busy_runner
# must fail there, by that cause:
#  1. busy: the glue as it shipped (no retry of a refused BEGIN or lone
#     statement, cbca5a7e) and RunState.store running the store call as
#     is: b's write lock held past the busy timeout stops b's runner
#     ("network runner stopped: ... database is locked").
#  2. scrub: checkpointSql as it shipped (cbca5a7e), throwing when a
#     reader blocks the truncating checkpoint: a reader across b's session
#     close stops b's runner ("purge: a reader blocked the WAL checkpoint").
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export CARGO_NET_OFFLINE=true
out=$PWD/out/busy-runner-negative
mkdir -p "$out"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/busy-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
parts="engine/core engine/renderer engine/sync engine/wire engine/world app tests/engine"

# run_mutant NAME STOP-MESSAGE FAILING-CHECK: build busy_runner in the
# mutated snapshot $tmp/NAME and require it to fail by that cause
run_mutant() {
  local name=$1 stop=$2 check=$3 dir=$tmp/$1 log=$out/$1.log rc
  (cd "$dir" && lake build busy_runner > "$out/$name-build.log" 2>&1) ||
    { tail -20 "$out/$name-build.log"; echo "busy_runner_negative: mutant $name does not build" >&2; exit 1; }
  set +e
  (cd "$dir" && timeout 300 .lake/build/bin/busy_runner "$out/$name-run") > "$log" 2>&1
  rc=$?
  set -e
  [ "$rc" != 0 ] ||
    { echo "busy_runner_negative: mutant $name passed busy_runner; the test does not catch it" >&2; exit 1; }
  grep -q "network runner stopped: .*$stop" "$log" ||
    { tail -20 "$log"; echo "busy_runner_negative: mutant $name failed, but not by: $stop" >&2; exit 1; }
  grep -q "^FAIL: $check" "$log" ||
    { tail -20 "$log"; echo "busy_runner_negative: mutant $name: the check \"$check\" did not catch it" >&2; exit 1; }
  echo "busy_runner_negative: caught $name: $(grep -c '^FAIL:' "$log") checks fail"
}

# 1. busy: the shipped glue, and the store call run as is
# shellcheck disable=SC2086
snapshot "$tmp/busy" $parts
git show cbca5a7e:engine/native/glue.c > "$tmp/busy/engine/native/glue.c"
tcp=$tmp/busy/engine/wire/Tcp.lean
grep -q '^  Store.retrying (act.run st.db)$' "$tcp" ||
  { echo "busy_runner_negative: RunState.store is not as expected; update mutant busy" >&2; exit 1; }
sed -i 's/^  Store.retrying (act.run st.db)$/  act.run st.db/' "$tcp"
run_mutant busy "database is locked" "busy: b's runner is still running"

# 2. scrub: checkpointSql throws when a reader blocks it
# shellcheck disable=SC2086
snapshot "$tmp/scrub" $parts
python3 - "$tmp/scrub/engine/core/Sqlite.lean" <<'PY'
import re, sys
p = sys.argv[1]
s = open(p).read()
old = '''def checkpointSql : SqlM F Unit := do
  let mode := col0 (← sqlQ (F := F) "PRAGMA journal_mode" #[])
  if (mode.head? >>= String.fromUTF8?) != some "wal" then return
  let rows ← sqlQ (F := F) "PRAGMA wal_checkpoint(TRUNCATE)" #[]
  if (rows[0]? >>= (·[0]?) >>= String.fromUTF8?) != some "0" then
    throw (IO.userError "purge: a reader blocked the WAL checkpoint; the purged bytes stay in the WAL until the next one")
'''
m = re.search(r"def checkpointSql : SqlM F Unit := do\n(?:  .*\n)+", s)
if not m:
    sys.exit("busy_runner_negative: checkpointSql is not as expected; update mutant scrub")
s = s[:m.start()] + old + s[m.end():]
open(p, "w").write(s)
PY
run_mutant scrub "a reader blocked the WAL checkpoint" "close: b's runner is still running"
