#!/usr/bin/env bash
# The executable suites: the scenario (real Ed25519, SQLite), the
# SQLite-vs-model differential, list queries against their meaning
# (querydiff), ops as wire bytes against a lying peer (wire), two nodes
# syncing through the driver (syncpair) and over localhost TCP through the
# runner (tcppair), the Noise handshake against its published vector, the
# connection family end to end (connection_check), purge (SQLite against
# the model, and a purged secret searched for in the database's files),
# attachment chunks against their Merkle root with forgeries and mutant
# verifiers (merkle_check), and kill -9 atomicity.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
if [ "${1:-}" = --phone-runtime ]; then
  python3 platforms/headless/build_runtime.py
  python3 tests/shipped/runtime.py | tee out/phone-runtime/runtime-check.log
  bin=$PWD/out/phone-runtime/bin
  out=out/phone-runtime/tests
else
  lake build sqlite_build scenario differential crash querydiff linkcheck lifecycle wire syncpair tcppair noise_check connection_check purge jointcp merkle_check
  bin=$PWD/.lake/build/bin
  out=out
fi
mkdir -p "$out"
"$bin"/sqlite_build
"$bin"/scenario "$out"/scenario
"$bin"/differential "$out"/differential "${SEEDS:-12}"
"$bin"/querydiff
"$bin"/linkcheck
"$bin"/lifecycle "$out"/lifecycle
"$bin"/wire "$out"/wire
"$bin"/syncpair
if [ "${SKIP_TCP:-0}" = 1 ]; then
  echo "SKIP TCP: tcppair jointcp (built; run outside the socket sandbox)"
else
  "$bin"/tcppair "$out"/tcppair
  "$bin"/jointcp "$out"/jointcp
fi
tests/engine/crypto_compat.sh
"$bin"/noise_check
"$bin"/connection_check
"$bin"/purge "$out"/purge "${SEEDS:-12}"
"$bin"/merkle_check
ENGINE_BIN="$bin" tests/engine/crash.sh "${CRASH_ROUNDS:-10}" "$out"/crash
if [ "${1:-}" != --phone-runtime ]; then tests/shipped/check.sh engine; fi
