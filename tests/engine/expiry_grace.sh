#!/usr/bin/env bash
# Actual admitted TCP input, Noise/SQLite, UI-first selection and silence expiry.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/expiry-grace
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.wire.ExpiryGraceLaws +tests.vacuity.ExpiryGrace epoch_ingress \
  >out/expiry-grace/build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/engine/ExpiryGraceAxioms.lean >out/expiry-grace/axioms.log 2>&1
python3 tests/engine/expiry_grace_negative.py
