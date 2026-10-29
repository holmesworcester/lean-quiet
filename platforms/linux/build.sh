#!/usr/bin/env bash
set -euo pipefail
top=$(cd "$(dirname "$0")/../.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
cd "$top/engine/native/crypto"
CARGO_TARGET_DIR=$PWD/target cargo build --release --offline
cd "$top"
test -f assets/font.bin
tools/noto_assets.sh
python3 platforms/linux/font.py assets/font.bin out/desktop/font.bin
lake build linux
