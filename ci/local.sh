#!/usr/bin/env bash
# Local CI: every part's gate, from the repository's top, on this
# machine (the workflow for a hosted runner is ci/workflow.yml, unused
# for now). Each part runs its own scripts, as its mise tasks do; output
# goes to out/ci/<part>.log, and each part keeps its own out/ for
# failure artifacts. Exits non-zero if any part fails; runs them all.
# `readme` checks the README's theorem links against the built parts
# (ci/proof-links.py), so it runs after them.
#   ci/local.sh [part...]   (default: engine mdns qr net app readme)
set -uo pipefail
top=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
logs=$top/out/ci
mkdir -p "$logs"
parts=("${@:-engine mdns qr net app readme}")
read -r -a parts <<< "${parts[*]}"
gate() {
  case $1 in
    engine) tests/check.sh && tests/run.sh ;;
    mdns|qr|net) tests/check.sh ;;
    app)
      [ -f assets/font.bin ] || tools/fetch_assets.sh
      lake build host two_nodes net_join cross arrival attach &&
        .lake/build/bin/host "${MESSAGES:-500}" out/host &&
        .lake/build/bin/two_nodes out/two &&
        .lake/build/bin/net_join out/net &&
        .lake/build/bin/cross out/cross &&
        .lake/build/bin/arrival out/arrival &&
        .lake/build/bin/attach out/attach &&
        tests/host_safe.sh &&
        tests/safe_negative.py &&
        tests/check.sh ;;
    readme) python3 ci/proof-links.py --check ;;
    *) echo "no part $1" >&2; return 2 ;;
  esac
}
failed=()
for p in "${parts[@]}"; do
  t0=$(date +%s)
  dir=$top/$p
  [ "$p" = readme ] && dir=$top
  if (cd "$dir" && gate "$p") > "$logs/$p.log" 2>&1; then
    echo "ok   $p ($(( $(date +%s) - t0 )) s)"
  else
    echo "FAIL $p ($(( $(date +%s) - t0 )) s): $logs/$p.log"
    failed+=("$p")
  fi
done
[ ${#failed[@]} -eq 0 ] || { echo "failed: ${failed[*]}"; exit 1; }
echo "all parts pass"
