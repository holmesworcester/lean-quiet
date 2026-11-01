#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ ${LQ_ENDPOINT_SCOPE:-0} != 1 ]]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env LQ_ENDPOINT_SCOPE=1 ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp \
    PATH=/mnt/storage/elan/bin:"$PATH" bash tests/endpoints/run.sh "$@"
fi
mkdir -p out/endpoints
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build endpoint_network +ops.connection.DiscoveryLaws >out/endpoints/build.log 2>&1 || {
  tail -80 out/endpoints/build.log; exit 1;
}
python3 tests/endpoints/network.py "${1:-lan}" "${@:2}"
