#!/usr/bin/env bash
# The proof gate: build every library (`lake build`) and require each law
# the audit lists (tests/Axioms.lean, every part's) to rest on Lean's
# standard axioms only (propext, Classical.choice, Quot.sound): no sorry,
# no added axiom.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build
lake build +Main  # the app's main, which tests/Wiring.lean walks from
out=$(lake env lean tests/Axioms.lean 2>&1)
echo "$out"
if grep -qE "sorryAx|error" <<<"$out"; then echo "sorry or error" >&2; exit 1; fi
n=$(grep -c "depends on axioms\|does not depend on any axioms" <<<"$out" || true)
want=$(grep -c "^#print axioms" tests/Axioms.lean)
[ "$n" -eq "$want" ] || { echo "expected $want axiom reports, got $n" >&2; exit 1; }
bad=$(grep "depends on axioms" <<<"$out" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
[ -z "$bad" ] || { echo "non-standard axioms: $bad" >&2; exit 1; }
echo "all $want laws rest on standard axioms only"
# Navigation (ops/app/NavLaws): the page and the back stack change only by
# a Nav step (App.St.withNav), so Nav's laws hold of every page change. The
# start state is a root, and a page's cache key (PageIn) only copies it.
nav=$(grep -rn -E '(backStack|\bpage) :=' --include=*.lean App.lean ops platforms |
  grep -v -e 'def St.withNav' -e '{ page := s.page,' -e 'cur := me.acc, page :=' || true)
[ -z "$nav" ] || { echo "a page change outside Nav: $nav" >&2; exit 1; }
echo "every page change is a Nav step"
