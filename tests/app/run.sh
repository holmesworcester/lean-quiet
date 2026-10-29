#!/usr/bin/env bash
# The app on the headless twin (platforms/headless): its own session
# (host: chaos, cold open, a fling to the top, send and react), two apps
# joined by link (two_nodes) and over real TCP on loopback (net_join), two
# communities named alike (cross), a photo arriving chunk by chunk
# (arrival), and photos over TCP (attach); a picture whose chunks land
# while its retry waits (pic_retry, with its negative controls). Also
# drives host.c's actual externs (host_twin_demo.sh), and checks the
# shipped SQLite and glue (tests/shipped). Screens, replies and databases
# in out/.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
[ -f assets/font.bin ] || tools/fetch_assets.sh
tests/app/bidi.sh
tests/app/bidi_host.sh
lake build host two_nodes net_join cross arrival attach inkless nodequeue pic_retry
tests/app/host_twin_demo.sh
.lake/build/bin/inkless
.lake/build/bin/nodequeue
.lake/build/bin/host "${MESSAGES:-500}" out/host
.lake/build/bin/two_nodes out/two
if [ "${SKIP_TCP:-0}" != 1 ]; then
  .lake/build/bin/net_join out/net
  .lake/build/bin/cross out/cross
else
  echo "SKIP net_join cross (TCP sandbox; both built)"
fi
.lake/build/bin/arrival out/arrival
if [ "${SKIP_TCP:-0}" != 1 ]; then .lake/build/bin/attach out/attach; else echo "SKIP attach (TCP sandbox; built)"; fi
# the desktop root without a window, then the Linux shell under Xvfb
tests/app/desktop.sh
if [ "${SKIP_X:-${SKIP_TCP:-0}}" != 1 ]; then platforms/linux/test.sh
else platforms/linux/build.sh && echo "SKIP linux e2e (no local X sockets; the shell built)"; fi
# navigation: each mutant of a rule must fail its law (ops/app/NavLaws)
tests/app/nav_negative.sh
.lake/build/bin/pic_retry out/pic_retry
tests/app/pic_retry_negative.sh
tests/shipped/check.sh app
tests/app/lifecycle.sh
tests/app/lifecycle_node.sh
tests/app/lifecycle_node_negative.sh
