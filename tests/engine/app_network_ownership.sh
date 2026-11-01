#!/usr/bin/env bash
# Real Runner ownership through App exceptions, with compiling controls.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mkdir -p out/app-network-ownership/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/app-network-ownership.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app platforms/headless platforms/desktop tests/engine
cp Quiet.lean "$work/"
ln -s "$PWD/assets" "$work/assets"
python3 tests/engine/app_network_ownership_negative.py "$work" "$PWD/out/app-network-ownership/negative"
