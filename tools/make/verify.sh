#!/bin/sh
# `make verify`: Lean's own checkers, which need Lean 4.35 or newer.
#   lake check       builds the default targets, replays them through the
#                    kernel, and fails on any axiom outside the standard ones
#   lake comparator  judges comparator.json's solution against its challenge:
#                    each named theorem proves the same statement, with only
#                    the permitted axioms
# Both run the project inside a bubblewrap sandbox (Linux). Runs both, then
# fails if either failed. VERIFY_DIR checks another project (the tests).
set -eu
top=${VERIFY_DIR:-$(cd "$(dirname "$0")/../.." && pwd)}
cd "$top"
: "${ELAN_HOME:=$HOME/.elan}"
export ELAN_HOME
PATH=$ELAN_HOME/bin:$PATH
export PATH

say() { printf '==> %s\n' "$*"; }
die() { printf 'make verify: %s\n' "$*" >&2; exit 1; }

command -v lake >/dev/null 2>&1 || die "no lake: run make install first"
v=$(lake --version 2>/dev/null | sed -n 's/.*Lean version \([0-9][0-9.]*\).*/\1/p')
[ -n "$v" ] || die "could not read Lean's version from: $(lake --version 2>&1)"
if [ "$(printf '%s\n4.35.0\n' "$v" | sort -V | head -n 1)" != 4.35.0 ]; then
  die "lake check and lake comparator need Lean 4.35 or newer; this project builds with Lean $v (lean-toolchain). Nothing was checked."
fi
[ -f comparator.json ] || die "no comparator.json in $top: lake comparator has no challenge to judge"
command -v bwrap >/dev/null 2>&1 ||
  die "lake check and lake comparator sandbox the project with bubblewrap: sudo apt-get install bubblewrap"

fail=
say "lake check (Lean $v): the default targets through the kernel, standard axioms only"
lake check || fail="$fail lake-check"
say "lake comparator: comparator.json"
lake comparator || fail="$fail lake-comparator"
[ -z "$fail" ] || die "failed:$fail"
say "verified: lake check and lake comparator pass"
