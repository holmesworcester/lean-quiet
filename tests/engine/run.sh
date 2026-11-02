#!/usr/bin/env bash
# The executable suites: the SQLite the phones ship, as built
# (sqlite_build), the codec that runs against its specification on random
# values and their mutants (codecdiff), the community family's bytes, ids
# and verdicts against main's before the op split (wiregolden), the scenario (real Ed25519,
# SQLite), the causal cut of removals over the trust rule's views
# (cut_check), the SQLite-vs-model differential, list queries against their
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
# --tcp: only the suites over localhost TCP (ci/local.sh's engine:tcp; its
# gate runs the rest with SKIP_TCP=1).
if [ "${1:-}" = --tcp ]; then
  lake build poolstarve tcppair jointcp
  mkdir -p out
  .lake/build/bin/poolstarve
  .lake/build/bin/tcppair out/tcppair
  .lake/build/bin/jointcp out/jointcp
  tests/engine/jointcp_busy.sh
  exit 0
fi
if [ "${1:-}" = --phone-runtime ]; then
  python3 platforms/headless/build_runtime.py
  python3 tests/shipped/runtime.py | tee out/phone-runtime/runtime-check.log
  bin=$PWD/out/phone-runtime/bin
  out=out/phone-runtime/tests
else
  lake build sqlite_build codecdiff wiregolden poolstarve scenario cut_check differential crash querydiff linkcheck lifecycle wire syncpair syncworld tcppair noise_check connection_check purge jointcp merkle_check costcheck window_check newest window_sync
  bin=$PWD/.lake/build/bin
  out=out
fi
mkdir -p "$out"
"$bin"/sqlite_build
"$bin"/codecdiff "${CODEC_VALUES:-200}"
# The community family's bytes, ids and verdicts are main's before the op split.
if [ -x "$bin"/wiregolden ]; then "$bin"/wiregolden | diff - tests/engine/wire-golden.txt && echo "wiregolden: identical"; fi
if [ "${SKIP_TCP:-0}" != 1 ]; then "$bin"/poolstarve; else echo "SKIP poolstarve (TCP sandbox)"; fi
"$bin"/scenario "$out"/scenario
"$bin"/cut_check "$out"/cut
"$bin"/differential "$out"/differential "${SEEDS:-12}"
"$bin"/querydiff
"$bin"/linkcheck
"$bin"/lifecycle "$out"/lifecycle
"$bin"/wire "$out"/wire
"$bin"/syncpair
"$bin"/syncworld
"$bin"/newest
"$bin"/window_sync
if [ "${SKIP_TCP:-0}" != 1 ]; then
  "$bin"/tcppair "$out"/tcppair
  "$bin"/jointcp "$out"/jointcp
  # and with its ports already taken, as under parallel CI
  [ "$bin" = "$PWD/.lake/build/bin" ] && tests/engine/jointcp_busy.sh
else
  echo "SKIP tcppair jointcp (TCP sandbox; both built)"
fi
tests/engine/crypto_compat.sh
mise run test:crypto-failure
"$bin"/noise_check
"$bin"/connection_check
"$bin"/purge "$out"/purge "${SEEDS:-12}"
"$bin"/merkle_check
"$bin"/window_check "$out"/windows "${SEEDS:-12}"
"$bin"/costcheck
ENGINE_BIN="$bin" tests/engine/crash.sh "${CRASH_ROUNDS:-10}" "$out"/crash
# The negative controls (tests/engine/controls.txt), unless --suites or
# --phone-runtime: ci/local.sh runs them as parts of their own, in parallel.
if [ "${1:-}" != --phone-runtime ] && [ "${1:-}" != --suites ]; then
  grep -v '^#' tests/engine/controls.txt | while IFS=$'\t' read -r name cmd; do
    [ -n "$name" ] || continue
    echo "engine control: $name"
    bash -c "$cmd" </dev/null
  done
fi
