#!/usr/bin/env bash
# Actual threaded Reader, original caps and SQLite through App rollback.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mkdir -p out/app-reader-ownership/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/app-reader-ownership.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/world engine/renderer app platforms/headless platforms/desktop tests/engine
cp Quiet.lean "$work/"
ln -s "$PWD/assets" "$work/assets"
python3 tests/engine/app_reader_ownership_negative.py "$work" "$PWD/out/app-reader-ownership/negative"
