#!/usr/bin/env bash
# Local CI: every part's gate, from the repository's top, on this
# machine (the workflow for a hosted runner is ci/workflow.yml, unused
# for now). Each part runs its own scripts, as its mise tasks do; output
# goes to out/ci/<part>.log, and each part keeps its own out/ for
# failure artifacts. Exits non-zero if any part fails; runs them all.
#   ci/local.sh [part...]   (default: engine mdns qr net app)
set -uo pipefail
top=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
logs=$top/out/ci
mkdir -p "$logs"
parts=("${@:-engine mdns qr net app}")
read -r -a parts <<< "${parts[*]}"
gate() {
  case $1 in
    engine) tests/check.sh && tests/run.sh ;;
    mdns|qr|net) tests/check.sh ;;
    app)
      [ -f assets/font.bin ] || tools/fetch_assets.sh
      lake build host two_nodes net_join arrival &&
        .lake/build/bin/host "${MESSAGES:-500}" out/host &&
        .lake/build/bin/two_nodes out/two &&
        .lake/build/bin/net_join out/net &&
        .lake/build/bin/arrival out/arrival &&
        tests/check.sh ;;
    *) echo "no part $1" >&2; return 2 ;;
  esac
}
failed=()
for p in "${parts[@]}"; do
  t0=$(date +%s)
  if (cd "$top/$p" && gate "$p") > "$logs/$p.log" 2>&1; then
    echo "ok   $p ($(( $(date +%s) - t0 )) s)"
  else
    echo "FAIL $p ($(( $(date +%s) - t0 )) s): $logs/$p.log"
    failed+=("$p")
  fi
done
[ ${#failed[@]} -eq 0 ] || { echo "failed: ${failed[*]}"; exit 1; }
echo "all parts pass"
