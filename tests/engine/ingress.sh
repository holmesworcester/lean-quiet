#!/usr/bin/env bash
# Linux/POSIX localhost TCP, SQLite, C/Rust/Lean toolchains; no external service.
# The named task builds every prerequisite and retains logs/databases under out/ingress.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
mkdir -p out/ingress
systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
  lake build engine.wire.IngressLaws engine.wire.IngressPriorityLaws engine.wire.IngressChurnLaws ingress_tcp \
  >out/ingress/build.log 2>&1
python3 tests/engine/ingress_negative.py
