#!/usr/bin/env bash
# The app on the headless twin (platforms/headless): its own session
# (host: chaos, cold open, a fling to the top, send and react), two apps
# joined by link (two_nodes) and over real TCP on loopback (net_join), two
# communities named alike (cross), a photo arriving chunk by chunk
# (arrival), and photos over TCP (attach); a picture whose chunks land
# while its retry waits (pic_retry, with its negative controls); the
# dogfood UX regressions on both scroll seams (ux, with its negative
# controls). Also
# drives host.c's actual externs (host_twin_demo.sh), and checks the
# shipped SQLite and glue (tests/shipped). Screens, replies and databases
# in out/.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
tests/app/noto.sh
bash tests/app/font_contract.sh
tests/app/cjk.sh
tests/app/bidi.sh
tests/app/bidi_host.sh
lake build host two_nodes net_join cross arrival attach inkless nodequeue pic_retry ux
mise run host:twin-demo
mise run host:seam
mise run host:slide
mise run host:translate
.lake/build/bin/inkless
tests/app/inkless_negative.sh
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
mise run host:desktop
if [ "${SKIP_X:-${SKIP_TCP:-0}}" != 1 ]; then mise run linux:e2e
else platforms/linux/build.sh && echo "SKIP linux e2e (no local X sockets; the shell built)"; fi
# navigation: each mutant of a rule must fail its law (ops/app/NavLaws)
tests/app/nav_negative.sh
.lake/build/bin/pic_retry out/pic_retry
tests/app/pic_retry_negative.sh
.lake/build/bin/ux out/ux
.lake/build/bin/ux out/ux-queued queued
tests/app/ux_negative.sh
tests/shipped/check.sh app
tests/app/lifecycle.sh
tests/app/lifecycle_node.sh
tests/app/lifecycle_node_negative.sh

mise run host:theme-restart
mise run host:theme-live
mise run host:theme-negative

mise run host:safe
mise run host:safe-negative
mise run host:desktop-negative
