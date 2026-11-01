#!/usr/bin/env bash
# Actual non-chat/chat frame sampling, native controls and kernel bound.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mkdir -p out/app-frame-times/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/app-frame-times.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app platforms/headless platforms/desktop tests/engine
cp Quiet.lean "$work/"
mkdir -p "$work/tests/vacuity"
cp tests/vacuity/FrameTimes.lean "$work/tests/vacuity/"
ln -s "$PWD/assets" "$work/assets"
python3 tests/engine/app_frame_times_negative.py "$work" "$PWD/out/app-frame-times/negative"
