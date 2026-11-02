#!/usr/bin/env bash
# The negative control of sqlite_build's durability check: with
# engine/core/Sqlite.lean back at `synchronous = NORMAL`, sqlite_build
# compiles and fails on that check, and on nothing else.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
out=$PWD/out/sync-full
mkdir -p "$out"
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build sqlite_build >"$out/build.log" 2>&1
.lake/build/bin/sqlite_build "$out/baseline" >"$out/baseline.log" 2>&1 ||
  { cat "$out/baseline.log"; echo "FAIL: sqlite_build fails before the mutation"; exit 1; }
. tests/snapshot.sh
scratch=$(mktemp -d "$TMPDIR/sync-full.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
snapshot "$scratch" engine/core tests/engine
src=$scratch/engine/core/Sqlite.lean
[ "$(grep -c '^PRAGMA synchronous = FULL;$' "$src")" = 1 ] ||
  { echo "FAIL: mutation anchor missing"; exit 1; }
sed -i 's/^PRAGMA synchronous = FULL;$/PRAGMA synchronous = NORMAL;/' "$src"
(cd "$scratch" && systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build sqlite_build) >"$out/mutant-build.log" 2>&1
if (cd "$scratch" && .lake/build/bin/sqlite_build "$scratch/out") >"$out/mutant.log" 2>&1; then
  cat "$out/mutant.log"; echo "FAIL: sqlite_build passed with synchronous = NORMAL"; exit 1
fi
cat "$out/mutant.log"
grep -q '^FAIL: a store opened as the app opens it syncs each commit' "$out/mutant.log" &&
  grep -q '^FAIL: so does a second connection to it' "$out/mutant.log" &&
  [ "$(grep -c '^FAIL' "$out/mutant.log")" = 2 ] ||
  { echo "FAIL: the mutant failed for another reason"; exit 1; }
echo "refused: synchronous = NORMAL (compiled; the durability check failed)"
