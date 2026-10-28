#!/usr/bin/env bash
# Each mutant changes a protocol rule so that one of the laws is false.
# Building the model must then fail. Runs in a scratch copy, never in
# this tree; the engine is shared read-only through a symlink.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
engine=$(cd ../engine && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/net-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
ln -s "$engine" "$tmp/engine"

mutant() {  # what file old new
  local what=$1 file=$2 old=$3 new=$4
  rm -rf -- "$tmp/lean-net"; mkdir -p "$tmp/lean-net"
  cp -r Net Net.lean lakefile.lean lake-manifest.json lean-toolchain "$tmp/lean-net/"
  python3 - "$tmp/lean-net/$file" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
  if (cd "$tmp/lean-net" && lake build Net >/dev/null 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  echo "refused by the proofs: $what"
}

# no_connection_before_approval is false: the first hello is answered.
mutant "the responder answers whether or not it trusts the sender" Net/Node.lean \
  "    if Trusts C n1 c i then" "    if True then"
# bootstrap is false: B trusts A only by ops it can only get over a session.
mutant "no link clause: the joiner trusts only by its ops" Net/Node.lean \
  "      (n.Anchored c p ∧ ¬ Known C n.ops c p ∧ ¬ Allowed C n.ops c n.me))" "      False)"
# bootstrap is false: A never holds the request, so nothing can approve it.
mutant "the bare door shut: a request is never read from a hello" Net/Node.lean \
  "  ofC c q = true ∧ ∃ u d e l t," "  False ∧ ∃ u d e l t,"
# bootstrap is false: the joiner's hello is never re-sent once lost.
mutant "no retry: a pending link sends no hello" Net/Node.lean \
  "  (n.links.filter fun l => !n.sessions.any fun s => decide (s = (l.c, l.dial))).map" \
  "  (([] : List Link).filter fun l => !n.sessions.any fun s => decide (s = (l.c, l.dial))).map"
echo "all mutants refused"
