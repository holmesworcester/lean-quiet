#!/usr/bin/env bash
# Local CI: every part's gate, from the repository's top, on this
# machine (the workflow for a hosted runner is ci/workflow.yml, unused
# for now). Each part runs its script under tests/, as its mise task
# does; output goes to out/ci/<part>.log, and failure artifacts stay in
# out/. Exits non-zero if any part fails; runs them all. `check` is the
# proof gate (every library builds; every law of tests/Axioms.lean rests
# on standard axioms only). `readme` checks the README's theorem links
# against the built tree (ci/proof-links.py), so it runs after them.
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
    check) tests/check.sh ;;
    engine) tests/engine/run.sh ;;
    runtime) tests/engine/run.sh --phone-runtime ;;
    mdns|qr|net) "tests/$1/check.sh" ;;
    app) tests/app/run.sh ;;
    readme) python3 ci/proof-links.py --check ;;
    reorg) python3 ci/reorg-imports.py --self-test ;;
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
