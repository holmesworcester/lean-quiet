#!/usr/bin/env bash
# Navigation's negative controls: each mutant breaks one rule of
# engine/renderer/Nav.lean or of App's steps over it, so that a law of Nav
# or of ops/app/NavLaws is false. Building the laws must then fail. Runs
# in a scratch copy, never in this tree (needs the tree built).
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/nav-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/renderer ops App.lean
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build ops.app.NavLaws >/dev/null 2>&1) || { echo "FAIL: the unmutated copy does not build"; exit 1; }

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
  if (cd "$tmp/w" && lake build ops.app.NavLaws >/dev/null 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  echo "refused by the proofs: $what"
}

# Nav.back_root is false: back at a root opens the page again on itself.
mutant "back at a root pushes the page" engine/renderer/Nav.lean \
  "  | [] => n" "  | [] => { n with stack := [n.page] }"
# Nav.go_inv is false: a page already under the shown one is pushed again.
mutant "opening a page under the shown one pushes it twice" engine/renderer/Nav.lean \
  "  else if p ∈ n.stack then" "  else if p ∈ n.stack ∧ False then"
# NavLaws.back_root is false: the old back, to the conversation at a root.
mutant "back at a root opens the conversation" App.lean \
  "def backSt (s : St) : St := { s.withNav (Nav.back s.nav) with" \
  "def backSt (s : St) : St := { s.withNav (if s.backStack.isEmpty then Nav.reset .chat else Nav.back s.nav) with"
# NavLaws.draft_back and back_open are false: back clears the draft.
mutant "back clears the composer's draft" App.lean \
  "with field := \"\", refusal := none, pageKey := none }" \
  "with field := \"\", text := \"\", refusal := none, pageKey := none }"
# NavLaws.back_switch is false: a switch keeps what was under the page.
mutant "a switch keeps the old back stack" App.lean \
  "  let s := { s.withNav (Nav.reset .home) with" "  let s := { s.withNav (Nav.go .home s.nav) with"
echo "all mutants refused"
