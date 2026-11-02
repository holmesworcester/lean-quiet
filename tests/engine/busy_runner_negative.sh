#!/usr/bin/env bash
# busy_runner's negative control: the runner as it shipped, its store call
# run as is (RunState.store without Store.retrying), in a scratch snapshot,
# never the working sources. Held past the busy timeout, b's write lock
# must stop b's runner ("network runner stopped: database is locked"), so
# busy_runner fails there; it passes on the running code (busy_runner).
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
snapshot "$tmp/base" engine/core engine/renderer engine/sync engine/wire engine/world app tests/engine
tcp=$tmp/base/engine/wire/Tcp.lean
grep -q '  Store.retrying (act.run st.db)$' "$tcp" ||
  { echo "busy_runner_negative: RunState.store is not as expected; update the mutant" >&2; exit 1; }
sed -i 's/^  Store.retrying (act.run st.db)$/  act.run st.db/' "$tcp"
(cd "$tmp/base" && lake build busy_runner > "$out/build.log" 2>&1) ||
  { tail -20 "$out/build.log"; echo "busy_runner_negative: the mutant does not build" >&2; exit 1; }
set +e
(cd "$tmp/base" && timeout 300 .lake/build/bin/busy_runner "$out/run") > "$out/run.log" 2>&1
rc=$?
set -e
if [ "$rc" = 0 ]; then
  echo "busy_runner_negative: the shipped runner passed busy_runner; the test does not catch it" >&2
  exit 1
fi
grep -q "network runner stopped: .*database is locked" "$out/run.log" ||
  { tail -20 "$out/run.log"; echo "busy_runner_negative: failed, but not by the runner stopping on a busy store" >&2; exit 1; }
grep -q "^FAIL: busy: b's runner is still running" "$out/run.log" ||
  { tail -20 "$out/run.log"; echo "busy_runner_negative: the runner-alive check did not catch it" >&2; exit 1; }
echo "busy_runner_negative: caught: the shipped runner stops on a busy store ($(grep -c '^FAIL:' "$out/run.log") checks fail)"
