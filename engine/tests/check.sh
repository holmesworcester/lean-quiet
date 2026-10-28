#!/usr/bin/env bash
# Build every proof and require each listed law to rest on Lean's
# standard axioms only (no sorry, no added axiom).
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
lake build Engine Community Connection
out=$(lake env lean tests/Axioms.lean)
echo "$out"
n=$(grep -c "depends on axioms\|does not depend on any axioms" <<<"$out")
want=$(grep -c "^#print axioms" tests/Axioms.lean)
[ "$n" -eq "$want" ] || { echo "expected $want axiom reports, got $n" >&2; exit 1; }
bad=$(grep "depends on axioms" <<<"$out" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
[ -z "$bad" ] || { echo "non-standard axioms: $bad" >&2; exit 1; }
echo "all $want laws rest on standard axioms only"
