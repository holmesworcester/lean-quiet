#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/close-ingress
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.wire.IngressFreezeLaws close_ingress >out/close-ingress/build.log 2>&1
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake env lean tests/vacuity/IngressFreeze.lean >out/close-ingress/kernel-witness.log 2>&1
python3 tests/engine/close_ingress_negative.py
