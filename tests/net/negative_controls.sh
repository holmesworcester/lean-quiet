#!/usr/bin/env bash
# Each mutant changes a protocol rule so that one of the laws is false.
# Building the model must then fail. Runs in a scratch copy, never in
# this tree.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/net-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
# what every mutant starts from (tests/snapshot.sh): the model and what it
# imports (the engine, sync, the Community family, and the renderer's
# character classes, which a profile's name is keyed by), and their part
# of the built tree
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire ops/sync ops/community ops/connection engine/renderer/Chars.lean
# the copy itself must build, or every mutant would look refused
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build Net >/dev/null 2>&1) || { echo "FAIL: the unmutated copy does not build"; exit 1; }

mutant() {  # what file old new
  local what=$1 file=$2 old=$3 new=$4
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/$file" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
  if (cd "$tmp/w" && lake build Net >/dev/null 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  echo "refused by the proofs: $what"
}

# no_connection_before_approval is false: the first hello is answered.
mutant "the responder answers whether or not it trusts the sender" ops/connection/bootstrap/Node.lean \
  "    if Trusts C n1 c i then" "    if True then"
# bootstrap is false: B trusts A only by ops it can only get over a session.
mutant "no link clause: the joiner trusts only by its ops" ops/connection/bootstrap/Node.lean \
  "      (n.Anchored c p ∧ ¬ Known C n.ops c p ∧ ¬ Allowed C n.ops c n.me))" "      False)"
# bootstrap is false: A never holds the request, so nothing can approve it.
mutant "the bare door shut: a request is never read from a hello" ops/connection/bootstrap/Node.lean \
  "  ofC c q = true ∧ ∃ u d e l t," "  False ∧ ∃ u d e l t,"
# bootstrap is false: the joiner's hello is never re-sent once lost.
mutant "no retry: a pending link sends no hello" ops/connection/bootstrap/Node.lean \
  "  (n.links.filter fun l => !n.sessions.any fun s => decide (s = (l.c, l.dial))).map" \
  "  (([] : List Link).filter fun l => !n.sessions.any fun s => decide (s = (l.c, l.dial))).map"
echo "all mutants refused"
