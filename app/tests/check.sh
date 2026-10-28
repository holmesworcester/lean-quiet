#!/usr/bin/env bash
# The proof gate: the app's theorems build, and rest on Lean's standard
# axioms only (propext, Classical.choice, Quot.sound).
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
lake build Quiet
out=$(lake env lean tests/Axioms.lean 2>&1)
echo "$out"
if echo "$out" | grep -E "depends on axioms" | grep -vE "\[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" | grep -q .; then
  echo "a theorem rests on a non-standard axiom" >&2; exit 1
fi
if echo "$out" | grep -qE "sorryAx|error"; then echo "sorry or error" >&2; exit 1; fi
n=$(echo "$out" | grep -c "depends on axioms\|does not depend on any axioms" || true)
echo "all $n theorems rest on standard axioms only"
