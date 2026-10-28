#!/usr/bin/env bash
# The app on the headless twin (platforms/headless): its own session
# (host: chaos, cold open, a fling to the top, send and react), two apps
# joined by link (two_nodes) and over real TCP on loopback (net_join), two
# communities named alike (cross), a photo arriving chunk by chunk
# (arrival), and photos over TCP (attach). Screens and databases in out/.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
[ -f assets/font.bin ] || tools/fetch_assets.sh
lake build host two_nodes net_join cross arrival attach inkless
.lake/build/bin/inkless
.lake/build/bin/host "${MESSAGES:-500}" out/host
.lake/build/bin/two_nodes out/two
.lake/build/bin/net_join out/net
.lake/build/bin/cross out/cross
.lake/build/bin/arrival out/arrival
.lake/build/bin/attach out/attach
