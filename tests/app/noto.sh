#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
tools/noto_assets.sh
python3 tests/app/noto_reference.py prepare out/noto
lake build noto
lake env lean --run tests/app/noto_kern.lean
.lake/build/bin/noto out/noto
python3 tests/app/noto_reference.py compare out/noto
