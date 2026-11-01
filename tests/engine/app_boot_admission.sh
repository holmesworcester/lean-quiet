#!/usr/bin/env bash
# Actual pre-boot Writer drain and App parking, with compiling controls.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mkdir -p out/app-boot-admission/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/app-boot-admission.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app platforms/headless platforms/desktop tests/engine
cp Quiet.lean "$work/"
ln -s "$PWD/assets" "$work/assets"
python3 tests/engine/app_boot_admission_negative.py "$work" "$PWD/out/app-boot-admission/negative"
