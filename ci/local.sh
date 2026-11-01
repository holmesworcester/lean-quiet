#!/usr/bin/env bash
# Local CI: the proofs first, then the tests in parallel, each isolated.
# The bootstrap-progress workflow uses these same gates when enabled.
#
#   ci/local.sh            the proofs, then every test part, 6 at once
#   ci/local.sh -j N       at most N test parts at once
#   ci/local.sh part...    just these gates, in order (any name below)
#
# 1. Proofs, in this tree, one after another; the first failure stops CI:
#    driver  this dispatcher's own checks (ci/local-test.py)
#    build   every library and executable, the native crypto, the assets
#    check   every law of tests/Axioms.lean rests on standard axioms only
#    layout  the op tree's layout, and its negative controls (ci/layout.py)
#    readme  the README's theorem links and the laws not yet about running
#            code, against tests/Wiring.lean (ci/proof-links.py)
#    reorg   the reorg's import rewriter (ci/reorg-imports.py --self-test)
# 2. Tests, at most N at once, longest first. A part writes only its own
#    out/ directories and scratch copies: a negative control's mutants work
#    in snapshots (tests/snapshot.sh), and TCP ports and X displays come
#    from the OS. The engine's suites are one part (engine:suites) and each
#    of its negative controls another (engine:<name>, tests/engine/
#    controls.txt). The app's controls edit sources in place, so its stages
#    run in three groups (app:1, app:2, app:3), each in its own copy of the
#    built tree ($TMPDIR/ci-app-*, deleted after; its out/ copied back).
#
# Each part has PART_TIMEOUT seconds (5400 by default): a part that hangs
# fails, its processes killed, and the others go on.
# Logs: out/ci/<part>.log. Exits non-zero if any part fails.
# `site` and `workspace` need Chromium's headless shell (CHROME, or
# Playwright's); `android-links` needs the Android SDK and an emulator image.
# SKIP_TCP=1 builds the TCP suites but omits their runs in a socket sandbox.
set -uo pipefail
top=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
logs=$top/out/ci
mkdir -p "$logs"
jobs=6
if [ "${1:-}" = -j ]; then jobs=$2; shift 2; fi

proofs=(driver build check layout readme reorg)
# longest first (minutes, measured on the shared box: qr 17, the app
# groups and engine:harden 10–15, the rest under 5)
tests=(qr app:2 app:1 app:3 engine:harden engine:fresh engine:suites
  $(grep -v '^#' "$top/tests/engine/controls.txt" 2>/dev/null | cut -f1 | grep -vx 'harden\|fresh' | sed 's/^/engine:/')
  mdns net visual zoom site workspace vacuity)
# the app's stages, in three groups, each run in its own copy of the tree
declare -A app_group=([app:1]="fonts input network" [app:2]="desktop navigation lifecycle"
  [app:3]="appearance safety components")

build_all() {
  (cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet) &&
  { [ -f assets/font.bin ] || tools/fetch_assets.sh; } && tools/noto_assets.sh &&
  lake build && lake build +Main \
    $(grep -oP '^lean_lib \K\S+' lakefile.lean) $(grep -oP '^lean_exe \K\S+' lakefile.lean)
}

gate() {
  case $1 in
    driver) mise run ci:driver-test ;;
    build) build_all ;;
    check) mise run check ;;
    engine) mise run test:engine ;;
    engine:suites) tests/engine/run.sh --suites ;;
    engine:*) local cmd
      cmd=$(awk -F'\t' -v n="${1#engine:}" '$1 == n { print $2 }' tests/engine/controls.txt)
      [ -n "$cmd" ] || { echo "no engine control ${1#engine:}" >&2; return 2; }
      bash -c "$cmd" ;;
    runtime) mise run test:engine-runtime ;;
    mdns|qr|net) mise run "test:$1" ;;
    app) mise run test:app && mise run windows:input ;;
    app:1|app:2) APP_TEST_ONLY="${app_group[$1]}" tests/app/run.sh ;;
    app:3) APP_TEST_ONLY="${app_group[$1]}" tests/app/run.sh && mise run windows:input ;;
    visual) mise run visual:compare && mise run visual:hover && mise run visual:composer ;;
    android-photo) mise run android:photo-e2e && mise run android:photo-lifecycle-e2e ;;
    android-release) mise run android:release-e2e ;;
    android-links) mise run android:links-e2e ;;
    site) mise run site:test ;;
    workspace) mise run workspace:e2e ;;
    ios-photo) mise run ios:photo-e2e ;;
    ios-ui) mise run ios:sim-e2e ;;
    ios-input-device|release-ios-input) mise run ios:input-device-e2e ;;
    windows-ui|release-windows) mise run windows:e2e ;;
    macos-ui|release-macos) mise run macos:e2e ;;
    android-ui) mise run android:twin-demo-e2e && mise run android:lifecycle-e2e ;;
    android-lifecycle) mise run android:lifecycle-e2e ;;
    zoom) mise run test:zoom ;;
    android-zoom) mise run android:zoom ;;
    release-zoom) mise run test:zoom && mise run android:zoom ;;
    pixel-scroll) mise run android:scroll-measure ;;
    readme) mise run readme:links ;;
    layout) mise run layout:check ;;
    reorg) mise run reorg:test ;;
    vacuity) mise run test:vacuity ;;
    crypto-failure) mise run test:crypto-failure ;;
    fairness) mise run test:fairness ;;
    bootstrap-progress) mise run test:bootstrap-progress ;;
    *) echo "no part $1" >&2; return 2 ;;
  esac
}

# One gate, as a process of its own (so a time limit kills all of it).
if [ "${1:-}" = --gate ]; then gate "$2"; exit $?; fi

# Run one part, logging to out/ci/<part>.log; app:N in a copy of the tree.
run() {
  local p=$1 t0 dir=$top log=$logs/${1//:/-}.log ok=0
  t0=$(date +%s)
  if [ -n "${app_group[$p]:-}" ]; then
    dir=$(mktemp -d "$TMPDIR/ci-${p//:/-}.XXXXXX")
    rsync -a --exclude=/out --exclude=/.git "$top/" "$dir/"
  fi
  (cd "$dir" && MISE_TRUSTED_CONFIG_PATHS="$dir" timeout -k 30 "${PART_TIMEOUT:-5400}" \
    bash "$dir/ci/local.sh" --gate "$p") > "$log" 2>&1 || ok=$?
  [ "$ok" = 124 ] && echo "timed out after ${PART_TIMEOUT:-5400} s" >> "$log"
  if [ "$dir" != "$top" ]; then
    [ -d "$dir/out" ] && rsync -a "$dir/out/" "$top/out/"
    case $dir in "$TMPDIR"/ci-app-*) rm -rf -- "$dir" ;; esac
  fi
  if [ "$ok" = 0 ]; then echo "ok   $p ($(( $(date +%s) - t0 )) s)"
  else echo "FAIL $p ($(( $(date +%s) - t0 )) s$([ "$ok" = 124 ] && echo ', timed out')): $log"; echo "$p" >> "$logs/failed"; fi
  return "$ok"
}

rm -f "$logs/failed"
t_start=$(date +%s)
if [ $# -gt 0 ]; then
  for p in "$@"; do run "$p"; done
else
  for p in "${proofs[@]}"; do
    run "$p" || { echo "the proofs failed at $p: no tests run"; exit 1; }
  done
  for p in "${tests[@]}"; do
    while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n; done
    run "$p" &
  done
  wait
fi
echo "($(( $(date +%s) - t_start )) s)"
if [ -s "$logs/failed" ]; then echo "failed: $(tr '\n' ' ' < "$logs/failed")"; exit 1; fi
if [ -n "${APP_TEST_FROM:-}" ]; then
  echo "all enabled checks pass; app resumed at $APP_TEST_FROM (earlier stages were NOT rerun)"
elif [ "${SKIP_TCP:-0}" = 1 ]; then
  echo "all enabled checks pass; TCP suites built but NOT run (SKIP_TCP=1)"
else
  echo "all parts pass"
fi
