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
# Resume a failed stage during local iteration. The default always runs all
# stages; the explicit resume is printed so it cannot look like a full run.
start=${APP_TEST_FROM:-fonts}
case "$start" in fonts|input|network|desktop|navigation|lifecycle|appearance|safety|components) ;;
  *) echo "unknown APP_TEST_FROM stage: $start" >&2; exit 2 ;;
esac
active=false
# APP_TEST_ONLY="fonts input …" runs just those stages: ci/local.sh runs
# the stages in groups, each group in its own copy of the tree, at once.
only=${APP_TEST_ONLY:-}
for s in $only; do
  case "$s" in fonts|input|network|desktop|navigation|lifecycle|appearance|safety|components) ;;
    *) echo "unknown APP_TEST_ONLY stage: $s" >&2; exit 2 ;;
  esac
done
stage() {
  if [ -n "$only" ]; then
    case " $only " in *" $1 "*) echo "app stage: $1"; return 0 ;; esac
    echo "SKIP app stage: $1 (APP_TEST_ONLY=$only)"
    return 1
  fi
  if [ "$1" = "$start" ]; then active=true; fi
  if "$active"; then echo "app stage: $1"; return 0; fi
  echo "SKIP previously tested app stage: $1 (APP_TEST_FROM=$start)"
  return 1
}
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
lake build host two_nodes link_devices net_join net_link cross arrival attach inkless nodequeue pic_retry ux
if stage fonts; then
tests/app/noto.sh
bash tests/app/font_contract.sh
mise run host:cjk
tests/app/bidi.sh
tests/app/bidi_host.sh
fi
if stage input; then
mise run host:twin-demo
mise run host:seam
mise run host:seam-negative
mise run host:slide
mise run host:translate
fi
if stage network; then
mise run host:write-admission
.lake/build/bin/inkless
tests/app/inkless_negative.sh
.lake/build/bin/nodequeue
.lake/build/bin/host "${MESSAGES:-500}" out/host
.lake/build/bin/two_nodes out/two
.lake/build/bin/link_devices out/link
if [ "${SKIP_TCP:-0}" != 1 ]; then
  mise run host:net-join
  mise run host:net-link
  .lake/build/bin/cross out/cross
else
  echo "SKIP net_join net_link cross (TCP sandbox; built)"
fi
.lake/build/bin/arrival out/arrival
if [ "${SKIP_TCP:-0}" != 1 ]; then .lake/build/bin/attach out/attach; else echo "SKIP attach (TCP sandbox; built)"; fi
fi
if stage desktop; then
# the desktop root without a window, then the Linux shell under Xvfb
mise run host:desktop
mise run host:photo
if [ "${SKIP_X:-${SKIP_TCP:-0}}" != 1 ]; then mise run linux:e2e; mise run linux:links
else platforms/linux/build.sh && echo "SKIP linux e2e and links (no local X sockets; the shell built)"; fi
fi
if stage navigation; then
# navigation: each mutant of a rule must fail its law (app/app/NavLaws)
tests/app/nav_negative.sh
.lake/build/bin/pic_retry out/pic_retry
tests/app/pic_retry_negative.sh
.lake/build/bin/ux out/ux
.lake/build/bin/ux out/ux-queued queued
tests/app/ux_negative.sh
tests/shipped/check.sh app
fi
if stage lifecycle; then
mise run host:lifecycle
mise run host:reader-request-negative
mise run host:lifecycle-node
mise run host:lifecycle-node-negative
fi

if stage appearance; then
mise run host:theme-restart
mise run host:theme-live
mise run host:theme-negative
fi

if stage safety; then
mise run host:safe
mise run host:safe-negative
mise run host:desktop-negative
if [ "${SKIP_X:-${SKIP_TCP:-0}}" != 1 ]; then mise run linux:links-negative
else echo "SKIP linux links negative controls (no local X sockets)"; fi
fi

if stage components; then
mise run test:hold-cache
mise run host:mobile-switcher
mise run test:people-reader
mise run host:component-demand
mise run host:component-demand-negative
fi
