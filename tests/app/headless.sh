#!/usr/bin/env bash
# The app on the headless twin, each program in one process with the real
# store, ops, queries and renderer: no sockets, no X, no wall-clock check,
# no source edited. Its session (cold open, a fling to the top, send and
# react), two apps joined by link, linked devices, a photo arriving chunk by chunk, a
# picture whose chunks land while its retry waits, the dogfood scroll
# seams, the node's queue and a frame drawn before the font loads.
# ci/local.sh runs it on every gate; tests/app/run.sh runs the same
# programs among the rest. Screens, replies and databases in out/.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
lake build host two_nodes link_devices arrival pic_retry ux nodequeue inkless
bin=.lake/build/bin
"$bin"/host "${MESSAGES:-500}" out/host
"$bin"/two_nodes out/two
"$bin"/link_devices out/link
"$bin"/arrival out/arrival
"$bin"/pic_retry out/pic_retry
"$bin"/ux out/ux
"$bin"/ux out/ux-queued queued
"$bin"/nodequeue
"$bin"/inkless
echo "headless: all pass"
