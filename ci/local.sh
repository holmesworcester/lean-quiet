#!/usr/bin/env bash
# Local CI: the gate (the proofs, then the fast tests at once), and with
# --full every other test part too.
#
#   ci/local.sh            the gate, before every push to main (minutes)
#   ci/local.sh --full     the gate, then every other part: nightly, and
#                          before a release
#   ci/local.sh -j N ...   at most N test parts at once (6 by default)
#   ci/local.sh part...    just these parts, in order (any name below)
#
# 1. The proofs, in this tree, one after another; the first failure stops CI:
#    driver  this dispatcher's own checks (ci/local-test.py)
#    build   every library and executable, so every law; the native
#            crypto; the assets
#    check   every law of tests/Axioms.lean rests on standard axioms only
#    layout  the op tree's layout, and its negative controls (ci/layout.py)
#    readme  the README's theorem links and the laws not yet about running
#            code, against tests/Wiring.lean (ci/proof-links.py)
#    reorg   the reorg's import rewriter (ci/reorg-imports.py --self-test)
# 2. The gate's tests, at once. Each is deterministic and runs in this
#    tree in one process at a time: no TCP, no X, no clock it must beat,
#    no source edited (the tree is checked unchanged after them):
#    vacuity        every law's hypotheses can hold together
#    visual         real ops, store, queries and renderer, drawn to pixels
#                   and compared with pinned libquiet screens
#    headless       the app's programs on the headless twin
#                   (tests/app/headless.sh)
#    engine:suites  the engine's suites (SQLite, codec, wire, sync, purge,
#                   Merkle, notices, costs, kill -9), without TCP
#    scale          a round's work at 1k, 10k and 100k items against the
#                   proven bounds, with negative controls (tests/scale)
# 3. --full: every other part, longest first. The negative controls'
#    mutants (engine:<name>, tests/engine/controls.txt; the app's, among
#    its stages), real TCP (engine:tcp, net, mdns), X and the desktop
#    shell, qr, zoom, site, the workspace. A mutant works in a snapshot
#    (tests/snapshot.sh); the app's stages edit sources in place, so they
#    run in three groups (app:1, app:2, app:3), each in its own copy of
#    the built tree ($TMPDIR/ci-app-*, deleted after; its out/ copied back).
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
jobs=6 full=0
while [ $# -gt 0 ]; do
  case $1 in
    -j) jobs=$2; shift 2 ;;
    --full) full=1; shift ;;
    *) break ;;
  esac
done

proofs=(driver build check layout readme reorg)
fast=(engine:suites visual headless vacuity scale)
# longest first (minutes, measured on the shared box: app:2 and app:3
# 40–55, qr 24, app:1 17, engine:harden 14, the rest under 10)
rest=(app:3 app:2 qr app:1 engine:harden engine:ref-publications engine:catalog-retry engine:fresh
  $(grep -v '^#' "$top/tests/engine/controls.txt" 2>/dev/null | cut -f1 |
    grep -vx 'harden\|ref-publications\|catalog-retry\|fresh' | sed 's/^/engine:/')
  engine:tcp mdns net zoom owned-input site workspace)
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
    driver) mise run ci:driver-test && python3 ci/readme-merge.py --self-test ;;
    build) build_all ;;
    check) mise run check ;;
    engine) mise run test:engine ;;
    engine:suites) SKIP_TCP=1 tests/engine/run.sh --suites ;;
    engine:tcp) tests/engine/run.sh --tcp ;;
    headless) mise run test:headless ;;
    scale) mise run test:scale ;;
    engine:*) local cmd
      cmd=$(awk -F'\t' -v n="${1#engine:}" '$1 == n { print $2 }' tests/engine/controls.txt)
      [ -n "$cmd" ] || { echo "no engine control ${1#engine:}" >&2; return 2; }
      bash -c "$cmd" ;;
    runtime) mise run test:engine-runtime ;;
    mdns|qr|net) mise run "test:$1" ;;
    app) mise run test:app && mise run windows:input && mise run test:owned-input ;;
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
    owned-input) mise run test:owned-input ;;
    android-owned-input) mise run android:owned-input-e2e ;;
    android-lifecycle) mise run android:lifecycle-e2e ;;
    zoom) mise run test:zoom ;;
    android-zoom) mise run android:zoom ;;
    release-zoom) mise run test:zoom && mise run android:zoom ;;
    pixel-scroll) mise run android:scroll-measure ;;
    readme) mise run readme:links ;;
    layout) mise run layout:check && python3 ci/exits.py --self-test && python3 ci/exits.py ;;
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
# Run test parts at once, at most $jobs, each in the background.
parallel() {
  for p in "$@"; do
    while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n; done
    run "$p" &
  done
  wait
}
if [ $# -gt 0 ]; then
  for p in "$@"; do run "$p"; done
else
  for p in "${proofs[@]}"; do
    run "$p" || { echo "the proofs failed at $p: no tests run"; exit 1; }
  done
  # the gate's tests edit nothing: the tree after them is the tree before
  tree() { git -C "$top" status --porcelain=v1 --untracked-files=no | sort; git -C "$top" diff HEAD | sha1sum; }
  before=$(tree)
  if [ "$full" = 1 ]; then parallel "${fast[@]}" "${rest[@]}"; else parallel "${fast[@]}"; fi
  if [ "$(tree)" != "$before" ]; then
    echo "FAIL a test edited the tree:"; git -C "$top" status --short --untracked-files=no
    echo tree >> "$logs/failed"
  fi
fi
echo "($(( $(date +%s) - t_start )) s)"
if [ -s "$logs/failed" ]; then echo "failed: $(tr '\n' ' ' < "$logs/failed")"; exit 1; fi
if [ -n "${APP_TEST_FROM:-}" ]; then
  echo "all enabled checks pass; app resumed at $APP_TEST_FROM (earlier stages were NOT rerun)"
elif [ "${SKIP_TCP:-0}" = 1 ]; then
  echo "all enabled checks pass; TCP suites built but NOT run (SKIP_TCP=1)"
elif [ $# -gt 0 ]; then
  echo "these parts pass: $*"
elif [ "$full" = 1 ]; then
  echo "all parts pass"
else
  echo "the gate passes (ci/local.sh --full runs the rest)"
fi
