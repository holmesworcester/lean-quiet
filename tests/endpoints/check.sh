#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ ${LQ_ENDPOINT_SCOPE:-0} != 1 ]]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env LQ_ENDPOINT_SCOPE=1 ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp \
    PATH=/mnt/storage/elan/bin:"$PATH" bash tests/endpoints/check.sh "$@"
fi
mkdir -p out/endpoints
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build endpoint_check +ops.connection.DiscoveryLaws >out/endpoints/check-build.log 2>&1
.lake/build/bin/endpoint_check | tee out/endpoints/check.log
lake env lean tests/endpoints/Axioms.lean >out/endpoints/axioms.log
! rg 'sorryAx|error:' out/endpoints/axioms.log
python3 tests/endpoints/mutations.py | tee out/endpoints/mutations.log
