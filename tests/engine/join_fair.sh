#!/usr/bin/env bash
# Prerequisites: Linux localhost TCP, Python3, C/Rust/Lean toolchains. No
# external service is used. SQLite databases, relay stats and failure logs
# remain under out/join-fair; a timed-out or panicking process fails the task.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/join-fair
lake build +engine.wire.PriorityLaws +engine.wire.LoopLaws +tests.vacuity.Priority join_fair >out/join-fair/build.log 2>&1
if [ "${SKIP_TCP:-0}" = 1 ]; then
  echo "SKIP join-fair runtime and strict-priority control (TCP sandbox; executable built)"
  exit 0
fi
python3 tests/engine/join_fair.py --out out/join-fair/baseline
python3 tests/engine/join_fair.py --out out/join-fair/ordered-hints --ordered-hints --join-only
python3 tests/engine/join_fair.py --out out/join-fair/first-hint-only \
  --dead-hints 1 --first-hint-only --expect-hint-starvation
scratch=$(mktemp -d "$TMPDIR/join-fair-negative.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
. tests/snapshot.sh
snapshot "$scratch" engine/core engine/wire engine/renderer ops/sync ops/community ops/connection tests/engine
python3 tests/engine/join_fair_negative.py "$scratch" "$PWD/out/join-fair" "$PWD"
