#!/usr/bin/env bash
# Each mutant changes a running protocol rule (the trust rule, a
# validator, the responder's answer) so that a law about it is false.
# Building the proofs must then fail. Runs in a scratch copy, never in
# this tree.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/net-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
# what every mutant starts from (tests/snapshot.sh): the running trust
# rule, validators and node reactions, with the laws about them, and
# their part of the built tree
. tests/snapshot.sh
snapshot "$tmp/base" engine app engine/renderer/Chars.lean
# the copy itself must build, or every mutant would look refused
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build +app.community.Proofs +app.Proofs >/dev/null 2>&1) || { echo "FAIL: the unmutated copy does not build"; exit 1; }

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
  if (cd "$tmp/w" && lake build +app.community.Proofs +app.Proofs >/dev/null 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  echo "refused by the proofs of running code: $what"
}

# connect_iff is false: the trust rule lets in any node.
mutant "the trust rule lets in every node" app/community/Commands.lean \
  "  pure (ls.any fun l => decide (l.2.2 = e))" "  pure true"
# admission_approved is false: an admission cites no approval of its request.
mutant "an admission needs no approval of its request" app/community/member/invite/request/approve/admit/Validate.lean \
  "    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ r = o.reqs.getD 1 .empty" \
  "    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c"
# answer_trusted is false: the responder answers whether or not it trusts the sender.
mutant "the responder answers whether or not it trusts the sender" app/Commands.lean \
  "  if !ok then return []" "  if false then return []"
echo "all mutants refused"
