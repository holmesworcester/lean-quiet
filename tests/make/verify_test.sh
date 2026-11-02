#!/usr/bin/env bash
# `make verify` (tools/make/verify.sh). On this repository, while it builds
# with Lean older than 4.35, it must fail and say why, checking nothing.
# On a small Lean 4.35 project (made here: a challenge with `sorry`, its
# solution, comparator.json) it must pass, and fail for each control: a
# solution proving a different statement (lake comparator), one resting on
# a new axiom (lake check and lake comparator), and no comparator.json.
# Needs the Lean 4.35.0 toolchain (elan downloads it once) and bubblewrap.
# Logs: out/make/verify-test/.
set -euo pipefail
top=$(cd "$(dirname "$0")/../.." && pwd)
export ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
export PATH="$ELAN_HOME/bin:$PATH"
logs=$top/out/make/verify-test
rm -rf "$logs"; mkdir -p "$logs"
w=$(mktemp -d "${TMPDIR:-/tmp}/lq-verify-test.XXXXXX")
trap 'rm -rf "$w"' EXIT
pass=0
ok() { pass=$((pass + 1)); echo "ok  $*"; }
fail() { echo "FAIL $*" >&2; echo "logs: $logs" >&2; exit 1; }

# This repository: Lean below 4.35 is refused with the reason.
if (cd "$top" && make verify) > "$logs/repo.log" 2>&1; then
  if grep -q 'Lean version 4\.3[0-4]' <(cd "$top" && lake --version 2>&1); then fail "make verify passed on Lean below 4.35"; fi
  ok "make verify passes on this repository (Lean 4.35 or newer)"
else
  if grep -q 'need Lean 4.35 or newer' "$logs/repo.log"; then
    grep -q 'Nothing was checked' "$logs/repo.log" || fail "the refusal does not say nothing was checked"
    ok "make verify on this repository (Lean below 4.35): refused, saying both need 4.35"
  else
    fail "make verify failed on this repository for another reason: $(tail -3 "$logs/repo.log")"
  fi
fi

# A small Lean 4.35 project.
project() {
  local d=$w/$1
  mkdir -p "$d"
  echo 'leanprover/lean4:v4.35.0' > "$d/lean-toolchain"
  cat > "$d/lakefile.lean" <<'EOF'
import Lake
open Lake DSL
package probe
lean_lib Challenge
@[default_target] lean_lib Solution
EOF
  cat > "$d/Challenge.lean" <<'EOF'
def double (n : Nat) : Nat := n + n
theorem double_even (n : Nat) : double n % 2 = 0 := sorry
EOF
  printf '%s\n' 'def double (n : Nat) : Nat := n + n' "$2" > "$d/Solution.lean"
  cat > "$d/comparator.json" <<'EOF'
{"challenge_module": "Challenge", "solution_module": "Solution",
 "theorem_names": ["double_even"], "definition_names": ["double"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
EOF
  (cd "$d" && lake build) > "$logs/$1-build.log" 2>&1 || fail "$1: the project does not build"
}
verify() { VERIFY_DIR=$w/$1 "$top/tools/make/verify.sh" > "$logs/$1.log" 2>&1; }

project good 'theorem double_even (n : Nat) : double n % 2 = 0 := by unfold double; omega'
verify good || fail "a correct solution failed make verify: $(tail -5 "$logs/good.log")"
grep -q 'verified: lake check and lake comparator pass' "$logs/good.log" || fail "the pass was not reported"
ok "a correct Lean 4.35 solution passes lake check and lake comparator"

project weaker 'theorem double_even (n : Nat) : double n % 1 = 0 := Nat.mod_one _'
if verify weaker; then fail "a solution proving a different statement passed"; fi
grep -q 'failed: lake-comparator' "$logs/weaker.log" || fail "the different statement was not caught by lake comparator"
ok "control: a solution proving a different statement fails lake comparator"

project axiom 'axiom cheat : False
theorem double_even (n : Nat) : double n % 2 = 0 := cheat.elim'
if verify axiom; then fail "a solution resting on a new axiom passed"; fi
grep -q 'failed: lake-check lake-comparator' "$logs/axiom.log" || fail "the new axiom was not caught by both checkers: $(tail -3 "$logs/axiom.log")"
ok "control: a solution resting on a new axiom fails lake check and lake comparator"

rm "$w/good/comparator.json"
if verify good; then fail "make verify passed without comparator.json"; fi
grep -q 'no comparator.json' "$logs/good.log" || fail "the missing comparator.json was not named"
ok "control: no comparator.json is refused"
echo "verify: $pass checks passed"
