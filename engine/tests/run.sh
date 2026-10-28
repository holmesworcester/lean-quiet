#!/usr/bin/env bash
# The executable suites: the scenario (real Ed25519, SQLite), the
# SQLite-vs-model differential, list queries against their meaning
# (querydiff), and kill -9 atomicity.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
lake build scenario differential crash querydiff linkcheck lifecycle
mkdir -p out
.lake/build/bin/scenario out/scenario
.lake/build/bin/differential out/differential "${SEEDS:-12}"
.lake/build/bin/querydiff
.lake/build/bin/linkcheck
.lake/build/bin/lifecycle out/lifecycle
tests/crash.sh "${CRASH_ROUNDS:-10}" out/crash
