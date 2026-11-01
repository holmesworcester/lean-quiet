#!/usr/bin/env bash
# Local CI: every part's gate, from the repository's top, on this
# machine. The ready bootstrap-progress workflow uses these same gates when enabled.
# Every gate calls its named
# Mise task; output goes to out/ci/<part>.log, and failure artifacts stay in
# out/. Exits non-zero if any part fails; runs them all. `check` is the
# proof gate (every library builds; every law of tests/Axioms.lean rests
# on standard axioms only). `readme` checks the README's theorem links
# against the built tree, and its list of laws not yet about running
# code against tests/Wiring.lean (ci/proof-links.py), so it runs after
# them.
# `layout` checks the op tree's layout (ci/layout.py --self-test).
# `reorg` checks the reorg's import rewriter for branches begun on the old
# layout (ci/reorg-imports.py --self-test).
#   ci/local.sh [part...]   (default: driver check layout engine mdns qr net endpoints app visual zoom site workspace readme reorg vacuity)
# `site` and `workspace` need Chromium's headless shell (CHROME, or Playwright's); `android-links`
# needs the Android SDK and an emulator image (it starts its own AVD).
# SKIP_TCP=1 builds the TCP suites but omits their runs in a socket sandbox.
# `runtime` is an additional gate on machines with Lean/libuv sources.
set -uo pipefail
top=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
logs=$top/out/ci
mkdir -p "$logs"
parts=("${@:-driver check layout engine mdns qr net endpoints app visual zoom site workspace readme reorg vacuity}")
read -r -a parts <<< "${parts[*]}"
gate() {
  case $1 in
    driver) mise run ci:driver-test ;;
    check) mise run check ;;
    engine) mise run test:engine ;;
    runtime) mise run test:engine-runtime ;;
    mdns|qr|net) mise run "test:$1" ;;
    app) mise run test:app && mise run windows:input && mise run test:owned-input ;;
    visual) mise run visual:compare && mise run visual:hover && mise run visual:composer ;;
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
    android-photo) mise run android:photo-e2e && mise run android:photo-lifecycle-e2e ;;
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
    # Peer endpoints: laws' concrete premises and mutation controls, then real
    # TCP/Noise/SQLite processes on this host (the phone and tailnet tasks need devices).
    endpoints) mise run test:endpoints && mise run test:endpoints-simultaneous && mise run test:endpoints-late && mise run test:endpoints-ops && mise run test:endpoints-invite && mise run test:endpoints-lan ;;
    bootstrap-progress) mise run test:bootstrap-progress ;;
    *) echo "no part $1" >&2; return 2 ;;
  esac
}
failed=()
for p in "${parts[@]}"; do
  t0=$(date +%s)
  if (cd "$top" && gate "$p") > "$logs/$p.log" 2>&1; then
    echo "ok   $p ($(( $(date +%s) - t0 )) s)"
  else
    echo "FAIL $p ($(( $(date +%s) - t0 )) s): $logs/$p.log"
    failed+=("$p")
  fi
done
[ ${#failed[@]} -eq 0 ] || { echo "failed: ${failed[*]}"; exit 1; }
if [ -n "${APP_TEST_FROM:-}" ]; then
  echo "all enabled checks pass; app resumed at $APP_TEST_FROM (earlier stages were NOT rerun)"
elif [ "${SKIP_TCP:-0}" = 1 ]; then
  echo "all enabled checks pass; TCP suites built but NOT run (SKIP_TCP=1)"
else
  echo "all parts pass"
fi
