#!/usr/bin/env bash
# The executable suites: the SQLite the phones ship, as built
# (sqlite_build), the codec that runs against its specification on random
# values and their mutants (codecdiff), the scenario (real Ed25519,
# SQLite), the SQLite-vs-model differential, list queries against their
# meaning (querydiff), ops as wire bytes against a lying peer (wire), two
# nodes syncing through the driver (syncpair), in the pure world the
# stream law is proven over (syncworld), and over localhost TCP through
# the runner (tcppair), the Noise handshake against its published vector,
# the connection family end to end (connection_check), purge (SQLite
# against the model, and a purged secret searched for in the database's
# files), attachment chunks against their Merkle root with forgeries and
# mutant verifiers (merkle_check), exact notices from the store's journal
# against windows read again, with the key-level and unnetted controls
# (window_check), the cost laws on the code that runs with their negative
# controls (costcheck), kill -9 atomicity, the sync hardening suite, and
# the shipped SQLite's and glue's checks (tests/shipped). With
# --phone-runtime, the suites run against Lean's runtime built from source
# with the phones' options (platforms/headless/build_runtime.py).
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
  lake build sqlite_build codecdiff poolstarve scenario differential crash querydiff linkcheck lifecycle wire syncpair syncworld tcppair noise_check connection_check purge jointcp merkle_check costcheck window_check
  bin=$PWD/.lake/build/bin
  out=out
fi
mkdir -p "$out"
"$bin"/sqlite_build
"$bin"/codecdiff "${CODEC_VALUES:-200}"
if [ "${SKIP_TCP:-0}" != 1 ]; then "$bin"/poolstarve; else echo "SKIP poolstarve (TCP sandbox)"; fi
"$bin"/scenario "$out"/scenario
"$bin"/differential "$out"/differential "${SEEDS:-12}"
"$bin"/querydiff
"$bin"/linkcheck
"$bin"/lifecycle "$out"/lifecycle
"$bin"/wire "$out"/wire
"$bin"/syncpair
"$bin"/syncworld
if [ "${SKIP_TCP:-0}" != 1 ]; then
  "$bin"/tcppair "$out"/tcppair
  "$bin"/jointcp "$out"/jointcp
else
  echo "SKIP tcppair jointcp (TCP sandbox; both built)"
fi
tests/engine/crypto_compat.sh
"$bin"/noise_check
"$bin"/connection_check
"$bin"/purge "$out"/purge "${SEEDS:-12}"
"$bin"/merkle_check
"$bin"/window_check "$out"/windows "${SEEDS:-12}"
"$bin"/costcheck
ENGINE_BIN="$bin" tests/engine/crash.sh "${CRASH_ROUNDS:-10}" "$out"/crash
if [ "${1:-}" != --phone-runtime ]; then
  tests/engine/harden.sh
  tests/engine/stateless.sh
  tests/engine/simplify.sh
  tests/engine/fresh.sh
  mise run test:read-plan
  mise run test:claim-tree
  tests/engine/restart.sh
  tests/shipped/check.sh engine
fi
