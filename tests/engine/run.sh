#!/usr/bin/env bash
# The executable suites: the codec that runs against its specification
# on random values and their mutants (codecdiff), the scenario (real
# Ed25519, SQLite), the SQLite-vs-model differential, list queries
# against their meaning (querydiff), ops as wire bytes against a lying
# peer (wire), two nodes syncing through the driver (syncpair), in the
# pure world the stream law is proven over (syncworld), and over
# localhost TCP through the runner (tcppair), the Noise handshake against
# its published vector, the connection family end to end
# (connection_check), purge (SQLite against the model, and a purged
# secret searched for in the database's files), attachment chunks against
# their Merkle root with forgeries and mutant verifiers (merkle_check),
# the cost laws on the code that runs with their negative controls
# (costcheck), exact notices from the store's journal against windows
# read again, with the key-level and unnetted controls (window_check),
# and kill -9 atomicity.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build codecdiff poolstarve scenario differential crash querydiff linkcheck lifecycle wire syncpair syncworld tcppair noise_check connection_check purge jointcp merkle_check costcheck window_check
mkdir -p out
.lake/build/bin/codecdiff "${CODEC_VALUES:-200}"
if [ "${SKIP_TCP:-0}" != 1 ]; then .lake/build/bin/poolstarve; else echo "SKIP poolstarve (TCP sandbox)"; fi
.lake/build/bin/scenario out/scenario
.lake/build/bin/differential out/differential "${SEEDS:-12}"
.lake/build/bin/querydiff
.lake/build/bin/linkcheck
.lake/build/bin/lifecycle out/lifecycle
.lake/build/bin/wire out/wire
.lake/build/bin/syncpair
.lake/build/bin/syncworld
if [ "${SKIP_TCP:-0}" != 1 ]; then
  .lake/build/bin/tcppair out/tcppair
  .lake/build/bin/jointcp out/jointcp
else
  echo "SKIP tcppair jointcp (TCP sandbox; both built)"
fi
tests/engine/crypto_compat.sh
.lake/build/bin/noise_check
.lake/build/bin/connection_check
.lake/build/bin/purge out/purge "${SEEDS:-12}"
.lake/build/bin/merkle_check
.lake/build/bin/costcheck
.lake/build/bin/window_check out/windows "${SEEDS:-12}"
tests/engine/crash.sh "${CRASH_ROUNDS:-10}" out/crash

tests/engine/harden.sh
