#!/usr/bin/env bash
# The headline laws (docs/HEADLINE.md): run tests/Headline.lean, which
# prints each law's axioms and spec surface and fails on a non-standard
# axiom; check the Comparator files (tests/comparator): the challenge
# elaborates with one `sorry` per theorem and nothing else, the solution
# is up to date, proves every theorem on standard axioms, and states each
# law word for word (`#same_statement`); from Lean v4.35, run
# `lake comparator` on them. Then the controls:
# a weakened restatement, a changed `match`, and a law resting on `sorry`
# must each be caught.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/headline.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

lake build
lake build +Main
lake build SpecTools

# The headline laws: axioms and surfaces.
out=$(lake env lean tests/Headline.lean 2>&1) || { echo "$out"; echo "tests/Headline.lean failed" >&2; exit 1; }
want=$(sed -n '/^#headline/,/^$/p' tests/Headline.lean | grep -cE '^  [A-Z]|^#headline [A-Z]' || true)
got=$(grep -c '^  at ' <<<"$out" || true)
[ "$got" -eq "$want" ] || { echo "$out"; echo "expected $want headline reports, got $got" >&2; exit 1; }
grep -E '^(headline|  at|  axioms|  surface|  review)' <<<"$out"
echo "headline: $got laws, each on standard axioms only"
# docs/HEADLINE.md's generated section states these numbers.
printf '%s\n' "$out" >"$tmp/headline.out"
python3 ci/headline.py --check "$tmp/headline.out"
# Its control: a changed surface count (318 read as 1318) must make it stale.
sed '0,/^  surface: \([0-9]*\)/s//  surface: 1\1/' "$tmp/headline.out" >"$tmp/stale.out"
if python3 ci/headline.py --check "$tmp/stale.out" 2>/dev/null; then
  echo "control not caught: a stale surface count in docs/HEADLINE.md" >&2; exit 1
fi
echo "control caught: a stale surface count in docs/HEADLINE.md"

# The Comparator files (tests/comparator): up to date; the challenge
# elaborates, and its only warnings are its sorrys.
python3 tests/comparator/solution.py --check
n=$(grep -c '^theorem ' tests/comparator/Challenge.lean)
out=$(lake env lean tests/comparator/Challenge.lean 2>&1) || { echo "$out"; echo "Challenge.lean failed" >&2; exit 1; }
other=$(grep -E 'warning|error' <<<"$out" | grep -v "declaration uses .sorry." || true)
s=$(grep -c "declaration uses .sorry." <<<"$out" || true)
[ -z "$other" ] && [ "$s" -eq "$n" ] || { echo "$out"; echo "Challenge.lean: expected $n sorry warnings and nothing else" >&2; exit 1; }

# The solution builds with no warning; each statement is its law's
# (Check.lean), on standard axioms.
out=$(lake build tests.comparator.Solution 2>&1) || { echo "$out"; echo "Solution.lean failed" >&2; exit 1; }
out=$(lake env lean tests/comparator/Solution.lean 2>&1) || { echo "$out"; echo "Solution.lean failed" >&2; exit 1; }
if grep -qE 'warning|error' <<<"$out"; then echo "$out"; echo "Solution.lean: a warning or an error" >&2; exit 1; fi
out=$(lake env lean tests/comparator/Check.lean 2>&1) || { echo "$out"; echo "Check.lean failed" >&2; exit 1; }
st=$(grep -c ' states ' <<<"$out" || true)
[ "$st" -eq "$n" ] || { echo "$out"; echo "Check.lean: $st of $n statements checked" >&2; exit 1; }
bad=$(grep -E '^Headline\.[A-Za-z_]+: \[' <<<"$out" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -e propext -e Classical.choice -e Quot.sound -e '' || true)
ax=$(grep -cE '^Headline\.[A-Za-z_]+: \[' <<<"$out" || true)
[ "$ax" -eq "$n" ] && [ -z "$bad" ] || { echo "$out"; echo "Check.lean: axioms $bad ($ax of $n audited)" >&2; exit 1; }
echo "comparator files: $n statements, each its law's, proved on standard axioms only"

# Comparator itself, from Lean v4.35 (lake comparator; it needs bwrap).
# Before that toolchain it does not exist: say so, and go on.
tc=$(sed 's/.*:v//' lean-toolchain)
if [ "$(printf '%s\n4.35.0\n' "$tc" | sort -V | head -1)" = 4.35.0 ]; then
  lake comparator --config tests/comparator/comparator.json ||
    { echo "lake comparator rejected the headline solution" >&2; exit 1; }
  echo "lake comparator: accepted"
  # Its control: the challenge with one statement weakened must be
  # rejected (exit 1; 2 would mean Comparator did not start).
  rc=0; lake comparator --config tests/comparator/comparator-weak.json >"$tmp/weak.out" 2>&1 || rc=$?
  [ "$rc" -eq 1 ] || { cat "$tmp/weak.out"; echo "control not caught: lake comparator exit $rc on a weakened challenge" >&2; exit 1; }
  echo "control caught: lake comparator rejects a weakened challenge"
else
  echo "lake comparator: skipped, Lean $tc has none (it comes in v4.35)"
fi

# Controls: each must be caught.
caught() { # file, what
  if lake env lean "$1" >"$tmp/out" 2>&1; then cat "$tmp/out"; echo "control not caught: $2" >&2; exit 1; fi
  echo "control caught: $2"
}
cat >"$tmp/Weak.lean" <<'EOF'
import tests.SpecSurface
import app.community.member.Proofs
theorem Headline.removal_authorized {C : Community.Crypto} {ops : Engine.Id → Option Engine.Op}
    {x c t u : Engine.Id} (h : Community.V C ops x (.removal c t u)) : t = u ∨ True := Or.inr trivial
#same_statement Headline.removal_authorized Community.removal_authorized
EOF
caught "$tmp/Weak.lean" "a weakened restatement of removal_authorized"
cat >"$tmp/Match.lean" <<'EOF'
import tests.SpecSurface
import app.community.member.remove.View
theorem Headline.writes_only_after_two (s : Remove.Step) (e : Remove.Ev) (u : Engine.Id)
    (h : (Remove.step s e).2 = some u) :
    (s = .second u ∨ ∃ why, s = .failed u why) ∧ (match e with | .yes => True | _ => True) :=
  ⟨(Remove.writes_only_after_two s e u h).1, by split <;> trivial⟩
#same_statement Headline.writes_only_after_two Remove.writes_only_after_two
EOF
caught "$tmp/Match.lean" "a restatement of writes_only_after_two with its match changed"
cat >"$tmp/Sorry.lean" <<'EOF'
import tests.SpecSurface
theorem unproven : 1 = 2 := by sorry
#headline unproven
EOF
caught "$tmp/Sorry.lean" "#headline on a law that rests on sorry"
