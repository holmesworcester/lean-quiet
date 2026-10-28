#!/usr/bin/env bash
# Each mutant changes the code that runs so that one of the engine's laws
# is false. Building the module that proves the law must then fail. Runs
# in a scratch copy, never in this tree.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/engine-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core
# the copy itself must build, or every mutant would look refused
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build engine.core.Union >/dev/null 2>&1) || { echo "FAIL: the unmutated copy does not build"; exit 1; }

mutant() {  # what target file old new
  local what=$1 target=$2 file=$3 old=$4 new=$5
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/$file" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:]
s = open(p).read()
assert s.count(old) == 1, f"mutant target not found once: {old!r}"
open(p, 'w').write(s.replace(old, new))
PY
  if (cd "$tmp/w" && lake build "$target" >/dev/null 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  echo "refused by the proofs: $what"
}

# mergeRuns_eq_sortPos is false: the union's lists are put end to end.
mutant "a union that concatenates its lists" engine.core.Union engine/core/Union.lean \
  "  rs.foldr (fun r acc => List.merge r acc posLE) []" "  rs.foldr (fun r acc => r ++ acc) []"
# mergeRuns_eq_sortPos is false: on a tie, a later list's row goes first.
mutant "a union whose merge takes a later list first on a tie" engine.core.Union engine/core/Union.lean \
  "  rs.foldr (fun r acc => List.merge r acc posLE) []" "  rs.foldr (fun r acc => List.merge acc r posLE) []"
# eval_oriented is false: a list read newest first comes oldest first.
mutant "a list that reads in the wrong direction" engine.core.Union engine/core/Query.lean \
  "  let ordered := if q.desc then inR.reverse else inR
  ⟨q.cut ordered" "  let ordered := if q.desc then inR else inR.reverse
  ⟨q.cut ordered"
# sortPos_eq_fast is false: the sort that runs reverses ties.
mutant "sortPos run as an unstable sort" engine.core.Query engine/core/Query.lean \
  "def sortPosFast {α} (l : List (Pos × α)) : List (Pos × α) := l.mergeSort posLE" \
  "def sortPosFast {α} (l : List (Pos × α)) : List (Pos × α) := l.mergeSort fun p q => p.1.cmp q.1 == .lt"
# inRange_unbounded is false: a list with no lower bound starts nowhere.
mutant "a range with no lower bound that holds nothing" engine.core.Query engine/core/Query.lean \
  "  (match q.after with | some a => p.cmp a == .gt | none => true) &&" \
  "  (match q.after with | some a => p.cmp a == .gt | none => false) &&"
# readPlan_cost is false: every read counts its whole range, however long.
mutant "a read that walks its whole list to count it" engine.core.Query engine/core/Query.lean \
  "  inRange := if q.after.isNone && q.before.isNone && others.isEmpty then none" \
  "  inRange := if false then none"
# readPlan_cost_range is false: a range's count ignores its cap.
mutant "a range's count that ignores its cap" engine.core.Query engine/core/Query.lean \
  "    else some (.count k others q.after q.before q.cap)" "    else some (.count k others q.after q.before 0)"
echo "all mutants refused"
