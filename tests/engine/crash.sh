#!/usr/bin/env bash
# Kill the writer (SIGKILL, by its recorded pid) mid-run; each time, what
# is on disk must be the state after whole batches, at least the batches
# it reported committed. No clock: the kill waits for the writer's report
# of a random batch k (whatever the disk's speed), so the kill lands
# while it writes batch k + 1 or later.
# Usage: tests/engine/crash.sh [rounds] [out_dir]
set -euo pipefail
cd "$(dirname "$0")/../.."
rounds=${1:-10}
# a directory of this run's own: two runs in one tree (say a gate beside a
# run by hand) must not delete each other's databases mid-round
mkdir -p "${2:-out/crash}"
out=$(mktemp -d "${2:-out/crash}/run.XXXXXX")
bin=${ENGINE_BIN:-.lake/build/bin}/crash
mid=0
for i in $(seq 1 "$rounds"); do
  db="$out/c$i.db"
  rm -f "$db" "$db-wal" "$db-shm"
  "$bin" write "$db" "$i" > "$out/write$i.log" &
  pid=$!
  k=$((1 + RANDOM % 10))
  # wait for "committed $k", or the writer's end, or 10 minutes
  for _ in $(seq 1 30000); do
    grep -qx "committed $k" "$out/write$i.log" 2>/dev/null && break
    kill -0 "$pid" 2>/dev/null || break
    sleep 0.02
  done
  kill -9 "$pid" 2>/dev/null || true
  wait "$pid" 2>/dev/null || true
  "$bin" check "$db" "$i" | tee "$out/check$i.log"
  told=$(grep -c '^committed ' "$out/write$i.log" || true)
  kept=$(sed -n 's/^on disk: \([0-9]*\) of.*/\1/p' "$out/check$i.log")
  if [ "${kept:-0}" -lt "$told" ]; then
    echo "FAIL: the writer reported $told batches committed, but $kept are on disk" >&2
    exit 1
  fi
  if grep -Eq "on disk: ([1-9][0-9]*) of" "$out/check$i.log" &&
     ! grep -Eq "on disk: ([0-9]+) of \1 batches" "$out/check$i.log"; then
    mid=$((mid + 1))
  fi
done
echo "killed mid-run in $mid of $rounds rounds"
if [ "$mid" -eq 0 ]; then
  echo "no round was killed mid-run; the test proved nothing" >&2
  exit 1
fi
