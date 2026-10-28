#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --offline --quiet)
lake build harden harden_tcp
.lake/build/bin/harden
if [ "${SKIP_TCP:-0}" != 1 ]; then
  .lake/build/bin/harden_tcp
else
  echo "SKIP harden_tcp (TCP sandbox; built)"
fi

tests/engine/harden_negative.sh
