#!/usr/bin/env bash
# Local CI: every part's gate, from the repository's top, on this
# machine and in .github/workflows/ci.yml. Every gate calls its named
# Mise task; output goes to out/ci/<part>.log, and failure artifacts stay in
# out/. Exits non-zero if any part fails; runs them all. `check` is the
# proof gate (every library builds; every law of tests/Axioms.lean rests
# on standard axioms only). `readme` checks the README's theorem links
# against the built tree, and its list of laws not yet about running
# code against tests/Wiring.lean (ci/proof-links.py), so it runs after
# them.
# `reorg` checks the reorg's import rewriter for branches begun on the old
# layout (ci/reorg-imports.py --self-test).
#   ci/local.sh [part...]   (default: check engine mdns qr net app readme reorg)
# SKIP_TCP=1 builds the TCP suites but omits their runs in a socket sandbox.
# `runtime` is an additional gate on machines with Lean/libuv sources.
set -uo pipefail
top=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
logs=$top/out/ci
mkdir -p "$logs"
parts=("${@:-check engine mdns qr net app readme reorg}")
read -r -a parts <<< "${parts[*]}"
gate() {
  case $1 in
    check) mise run check ;;
    engine) mise run test:engine ;;
    runtime) mise run test:engine-runtime ;;
    mdns|qr|net) mise run "test:$1" ;;
    app) mise run test:app ;;
    readme) mise run readme:links ;;
    reorg) mise run reorg:test ;;
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
if [ "${SKIP_TCP:-0}" = 1 ]; then
  echo "all enabled checks pass; TCP suites built but NOT run (SKIP_TCP=1)"
else
  echo "all parts pass"
fi
