#!/usr/bin/env bash
# Local CI: the gate (the proofs, then the fast tests at once), and with
# --full every other test part too.
#
#   ci/local.sh            the gate, before every push to main (minutes)
#   ci/local.sh --full     the gate, then every other part: nightly, and
#                          before a release
#   ci/local.sh -j N ...   at most N test parts at once (6 by default)
#   ci/local.sh part...    just these parts, in order (any name below)
#   ci/local.sh --list [--full]   the parts, in the order they would run
#
# 1. The proofs, in this tree, one after another; the first failure stops CI:
#    driver  this dispatcher's own checks (ci/local-test.py), and the
#            negative controls' snapshot (tests/snapshot_test.sh)
#    build   every library and executable, so every law; the native
#            crypto; the assets
#    check   every law of tests/Axioms.lean rests on standard axioms only
#    layout  the op tree's layout, and its negative controls (ci/layout.py)
#    readme  the README's theorem links and the laws not yet about running
#            code, against tests/Wiring.lean (ci/proof-links.py); the proof
#            tree, from that run's graph (docs/PROOF-TREE.md, ci/proof-tree.py);
#            and the premise tables (ci/premises.py): no ✅ row resting on a
#            [trusted] or [model] premise, no untagged premise, every
#            assumption tagged with both its sides (or in the baseline)
#    reorg   the reorg's import rewriter (ci/reorg-imports.py --self-test)
#    headline  the headline laws' axioms and spec surfaces, docs/HEADLINE.md
#            against them, the Comparator files, and `lake comparator` on
#            the root comparator.json and its weakened control
#            (tests/headline.sh)
# 2. The gate's tests, at once. Each is deterministic and runs in this
#    tree in one process at a time: no TCP, no X, no clock it must beat,
#    no source edited (the tree is checked unchanged after them):
#    vacuity        every law's hypotheses can hold together
#    visual         real ops, store, queries and renderer, drawn to pixels
#                   and compared with pinned libquiet screens
#    headless       the app's programs on the headless twin
#                   (tests/app/headless.sh)
#    forensics      the proofslop forensics tool's deterministic pass:
#                   standard axioms only, no kernel escape hatch, no
#                   statement smell outside ci/forensics-baseline.txt
#    engine:suites  the engine's suites (SQLite, codec, wire, sync, purge,
#                   Merkle, notices, costs, kill -9), without TCP
#    make:assets    make install's assets step and its controls, and the
#                   pinned assets tarball against this tree (stale: pack
#                   and publish it again, docs/BUILD.md)
#    scale          a round's work and the capped write turn at 1k, 10k
#                   and 100k items against the proven bounds, with
#                   negative controls (tests/scale)
# 3. --full: every other part, 4 at once (the box is shared), longest first (by each part's
#    time on the last run, out/ci/times.tsv). The negative controls'
#    mutants (engine:<name>, tests/engine/controls.txt), real TCP
#    (engine:tcp, net, mdns), X and the desktop shell, qr, zoom, site, the
#    workspace, `make install && make run` and `make demo` from a fresh
#    clone in Docker (make:clean-room), make demo under Xvfb with its
#    negative control (make:demo), make verify on a Lean 4.35 project
#    (make:verify), the headline laws under their own names
#    (headline:own: `lake comparator` on tests/comparator/own-*.json),
#    and each of the app's checks (app:<part>, tests/app/
#    parts.txt; a part with cases, app:<part>/<case>, one part a case).
#    An engine mutant works in a snapshot (tests/snapshot.sh); an app part
#    may edit sources in place, so each runs in its own copy of the built
#    tree ($TMPDIR/ci-app-*, deleted after; its out/ copied back).
#
# Each part has PART_TIMEOUT seconds (5400 by default): a part that hangs
# fails, its processes killed, and the others go on.
# Logs: out/ci/<part>.log. Exits non-zero if any part fails.
# `site` and `workspace` need Chromium's headless shell (CHROME, or
# Playwright's); `android-links` needs the Android SDK and an emulator image;
# `make:clean-room` needs Docker and network access (tests/make/clean_room.sh);
# `make:verify` needs the Lean 4.35.0 toolchain and bubblewrap.
# SKIP_TCP=1 builds the TCP suites but omits their runs in a socket sandbox.
set -uo pipefail
top=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
logs=$top/out/ci
mkdir -p "$logs"
jobs= full=0 list=0
while [ $# -gt 0 ]; do
  case $1 in
    -j) jobs=$2; shift 2 ;;
    --full) full=1; shift ;;
    --list) list=1; shift ;;
    *) break ;;
  esac
done

[ -n "$jobs" ] || jobs=$([ "$full" = 1 ] && echo 4 || echo 6)

proofs=(driver build check layout readme reorg headline)
fast=(engine:suites visual headless vacuity make:assets scale forensics)
# The app's parts (tests/app/parts.txt): a part with cases in slices, at
# most CASE_LANES (6), app:<part>/<k>; slice k is every case whose line
# number is k modulo the number of slices (slice).
slices() { local n; n=$(cd "$top" && tests/app/run.sh --cases "$1" | wc -l); echo $(( n < ${CASE_LANES:-6} ? n : ${CASE_LANES:-6} )); }
slice() { local m; m=$(slices "$1"); (cd "$top" && tests/app/run.sh --cases "$1") | awk -v k="$2" -v m="$m" '(NR - 1) % m == k - 1'; }
app_parts() {
  local st name cmd kind k
  while IFS=$'\t' read -r st name cmd kind; do
    case $st in ''|'#'*) continue ;; esac
    if [ "${kind:-}" = cases ]; then
      for k in $(seq 1 "$(slices "$name")"); do echo "app:$name/$k"; done
    else
      echo "app:$name"
    fi
  done < "$top/tests/app/parts.txt"
}
rest=(make:clean-room $(app_parts) windows-input qr
  $(grep -v '^#' "$top/tests/engine/controls.txt" 2>/dev/null | cut -f1 | grep . | sed 's/^/engine:/')
  engine:tcp mdns net make:demo zoom owned-input site workspace make:verify headline:own)
# Longest first, by each part's last recorded time (out/ci/times.tsv, else
# ci/times.tsv); a part not yet timed counts as 10 minutes.
longest_first() {
  local p t
  for p in "$@"; do
    t=$(cat "$top/ci/times.tsv" "$logs/times.tsv" 2>/dev/null |
      awk -F'\t' -v p="$p" '$1 == p { t = $2 } END { print t + 0 }')
    [ "${t:-0}" -gt 0 ] || t=600
    printf '%s\t%s\n' "$t" "$p"
  done | sort -t$'\t' -k1,1rn | cut -f2
}

build_all() {
  (cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet) &&
  { [ -f assets/font.bin ] || tools/fetch_assets.sh; } && tools/noto_assets.sh &&
  lake build && lake build +Main \
    $(grep -oP '^lean_lib \K\S+' lakefile.lean) $(grep -oP '^lean_exe \K\S+' lakefile.lean)
}

gate() {
  case $1 in
    driver) mise run ci:driver-test && python3 ci/readme-merge.py --self-test && mise run test:snapshot ;;
    build) build_all ;;
    check) mise run check ;;
    engine) mise run test:engine ;;
    engine:suites) SKIP_TCP=1 tests/engine/run.sh --suites ;;
    engine:tcp) tests/engine/run.sh --tcp ;;
    headless) mise run test:headless ;;
    engine:*) local cmd
      cmd=$(awk -F'\t' -v n="${1#engine:}" '$1 == n { print $2 }' tests/engine/controls.txt)
      [ -n "$cmd" ] || { echo "no engine control ${1#engine:}" >&2; return 2; }
      bash -c "$cmd" ;;
    runtime) mise run test:engine-runtime ;;
    mdns|qr|net) mise run "test:$1" ;;
    app) mise run test:app && mise run windows:input && mise run test:owned-input ;;
    app:*/*) local q=${1#app:}
      CI_LANE=1 tests/app/run.sh --part "${q%%/*}" $(slice "${q%%/*}" "${q#*/}") ;;
    app:*) CI_LANE=1 tests/app/run.sh --part "${1#app:}" ;;
    windows-input) mise run windows:input ;;
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
    make:assets) mise run make:assets-test ;;
    make:clean-room) mise run make:clean-room ;;
    make:verify) mise run make:verify-test ;;
    make:demo) mise run make:demo-e2e && mise run make:demo-negative ;;
    readme) mise run readme:links && mise run premises:check ;;
    layout) mise run layout:check && python3 ci/exits.py --self-test && python3 ci/exits.py ;;
    reorg) mise run reorg:test ;;
    headline) mise run test:headline ;;
    headline:own) mise run test:headline-own ;;
    vacuity) mise run test:vacuity ;;
    scale) mise run test:scale ;;
    forensics) mise run forensics:check ;;
    crypto-failure) mise run test:crypto-failure ;;
    fairness) mise run test:fairness ;;
    bootstrap-progress) mise run test:bootstrap-progress ;;
    *) echo "no part $1" >&2; return 2 ;;
  esac
}

if [ "$list" = 1 ]; then
  printf '%s\n' "${proofs[@]}" "${fast[@]}"
  [ "$full" = 1 ] && longest_first "${rest[@]}"
  exit 0
fi

# One gate, as a process of its own (so a time limit kills all of it).
if [ "${1:-}" = --gate ]; then gate "$2"; exit $?; fi

# Run one part, logging to out/ci/<part>.log; app:N in a copy of the tree.
run() {
  local p=$1 t0 dir=$top safe=${1//[:\/]/-} ok=0 log
  log=$logs/$safe.log
  t0=$(date +%s)
  case $p in app:*)
    dir=$(mktemp -d "$TMPDIR/ci-$safe.XXXXXX")
    rsync -a --exclude=/out --exclude=/.git "$top/" "$dir/" ;;
  esac
  (cd "$dir" && MISE_TRUSTED_CONFIG_PATHS="$dir" timeout -k 30 "${PART_TIMEOUT:-5400}" \
    bash "$dir/ci/local.sh" --gate "$p") > "$log" 2>&1 || ok=$?
  [ "$ok" = 124 ] && echo "timed out after ${PART_TIMEOUT:-5400} s" >> "$log"
  if [ "$dir" != "$top" ]; then
    [ -d "$dir/out" ] && rsync -a "$dir/out/" "$top/out/"
    case $dir in "$TMPDIR"/ci-app-*) rm -rf -- "$dir" ;; esac
  fi
  printf '%s\t%s\n' "$p" "$(( $(date +%s) - t0 ))" >> "$logs/times.tsv"
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
  if [ "$full" = 1 ]; then parallel $(longest_first "${rest[@]}") "${fast[@]}"; else parallel "${fast[@]}"; fi
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
