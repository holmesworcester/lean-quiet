#!/usr/bin/env bash
# Kill the writer (SIGKILL, by its recorded pid) at random moments; each
# time, what is on disk must be the state after whole batches.
# Usage: tests/engine/crash.sh [rounds] [out_dir]
set -euo pipefail
cd "$(dirname "$0")/../.."
rounds=${1:-10}
out=${2:-out/crash}
bin=${ENGINE_BIN:-.lake/build/bin}/crash
mkdir -p "$out"
mid=0
for i in $(seq 1 "$rounds"); do
  db="$out/c$i.db"
  rm -f "$db" "$db-wal" "$db-shm"
  "$bin" write "$db" "$i" > "$out/write$i.log" &
  pid=$!
  ms=$((20 + RANDOM % 200))
  sleep "$(printf '0.%03d' "$ms")"
  kill -9 "$pid" 2>/dev/null || true
  wait "$pid" 2>/dev/null || true
  "$bin" check "$db" "$i" | tee "$out/check$i.log"
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
