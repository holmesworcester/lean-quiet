#!/usr/bin/env bash
# Accepted writer ownership, empty real maintenance output, and OS log failures.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
[ "$(uname -s)" = Linux ] && [ -c /dev/full ] || {
  echo 'writer diagnostic gate requires Linux /dev/full' >&2; exit 1;
}
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
mkdir -p out/writer-job-retry/negative
source tests/snapshot.sh
work=$(mktemp -d "$TMPDIR/writer-job-retry.XXXXXX")
trap 'rm -rf "$work"' EXIT
snapshot "$work" engine/core engine/wire engine/sync engine/renderer app platforms/headless platforms/desktop tests/engine
cp Quiet.lean "$work/"
ln -s "$PWD/assets" "$work/assets"
python3 tests/engine/writer_job_retry_negative.py "$work" "$PWD/out/writer-job-retry/negative"
