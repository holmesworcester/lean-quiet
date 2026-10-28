#!/usr/bin/env bash
# Each mutant changes the code that runs so that one law is false (or,
# for NoDerive, so that an intent derives a key). Building the module
# that proves the law (or runs the check) must then fail. Runs in a
# scratch copy, never in this tree.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/engine-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
# what every mutant starts from (tests/snapshot.sh): the engine, the
# Community family and what its views import, and their built tree
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/renderer ops/sync ops/community ops/connection ops/app
targets=(engine.core.Query engine.core.Union ops.community.Compose ops.community.Laws
  ops.community.message.Order ops.community.NoDerive)
# the copy itself must build, or every mutant would look refused
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build "${targets[@]}" >/dev/null 2>&1) || { echo "FAIL: the unmutated copy does not build"; exit 1; }

# A mutant is refused by its law: the build must fail, and with an error
# inside that law's declaration (law: file:name; for NoDerive, its
# command), not merely somewhere: a proof script that breaks around a
# law still true is not a refusal.
mutant() {  # what target law file old new [old new ...]: each old occurs once
  local what=$1 target=$2 law=$3 file=$4
  shift 4
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w/$file" "$@" <<'PY'
import sys
p, *pairs = sys.argv[1:]
s = open(p).read()
for old, new in zip(pairs[::2], pairs[1::2]):
    assert s.count(old) == 1, f"mutant target not found once: {old!r}"
    s = s.replace(old, new)
open(p, 'w').write(s)
PY
  if (cd "$tmp/w" && lake build "$target" > "$tmp/log" 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  if python3 - "$tmp/w" "$law" "$tmp/log" <<'PY'
import re, sys
w, law, log = sys.argv[1:]
path, name = law.rsplit(":", 1)
lines = open(f"{w}/{path}").read().split("\n")
top = re.compile(r"^(theorem|def|lemma|instance|structure|inductive|abbrev|@\[|/--|/-!|#|end\b|section|namespace|variable|open|elab|omit)")
start = next(i for i, l in enumerate(lines)
             if re.match(rf"^(@\[csimp\] )?theorem {re.escape(name)}\b", l) or l.startswith(name))
end = next((i for i in range(start + 1, len(lines)) if top.match(lines[i])), len(lines))
errs = [int(m.group(1)) for m in re.finditer(rf"^error: {re.escape(path)}:(\d+):", open(log).read(), re.M)]
sys.exit(0 if any(start < e <= end for e in errs) else 1)
PY
  then echo "refused by ${law##*:}: $what"
  else echo "FAIL: refused, but not by ${law##*:}: $what"; grep -m3 '^error' "$tmp/log"; exit 1
  fi
}

## Sorting: no read sorts

# mergeRuns_eq_sortPos is false: the union's lists are put end to end.
mutant "a union that concatenates its lists" engine.core.Union engine/core/Union.lean:mergeRuns_eq_sortPos engine/core/Union.lean \
  "  rs.foldr (fun r acc => List.merge r acc posLE) []" "  rs.foldr (fun r acc => r ++ acc) []"
# mergeRuns_eq_sortPos is false: on a tie, a later list's row goes first.
mutant "a union whose merge takes a later list first on a tie" engine.core.Union engine/core/Union.lean:mergeRuns_eq_sortPos engine/core/Union.lean \
  "  rs.foldr (fun r acc => List.merge r acc posLE) []" "  rs.foldr (fun r acc => List.merge acc r posLE) []"
# union_rows (and so union_sorted, which rests on it) is false: a
# newest-first union comes oldest first.
mutant "a union that does not turn its merge back" engine.core.Union engine/core/Union.lean:union_rows engine/core/Union.lean \
  "  let ordered := orient desc (mergeRuns (as.map fun a => orient desc a.rows))" \
  "  let ordered := mergeRuns (as.map fun a => orient desc a.rows)"
# eval_oriented and eval_strict are false (their general form, eval_pairwise):
# a list read newest first comes oldest first.
mutant "a list that reads in the wrong direction" engine.core.Union engine/core/Union.lean:eval_pairwise engine/core/Query.lean \
  "  let ordered := if q.desc then inR.reverse else inR
  ⟨q.cut ordered" "  let ordered := if q.desc then inR else inR.reverse
  ⟨q.cut ordered"
# order_total is false: readable merges its receipt lists read the other way.
# (its unfolding, eval_readable, restated to match, as a change would)
mutant "readable reads its receipts in the other direction" ops.community.message.Order ops/community/message/Order.lean:order_total ops/community/Intents.lean \
  "(received.byKey.query [c, kid] limit desc (after.map" "(received.byKey.query [c, kid] limit (!desc) (after.map" \
  "(received.byKey.query [c, kid] lim desc (after.map" "(received.byKey.query [c, kid] lim (!desc) (after.map"
# sortPos_eq_fast is false: the sort that runs reverses ties.
mutant "sortPos run as an unstable sort" engine.core.Query engine/core/Query.lean:sortPos_eq_fast engine/core/Query.lean \
  "def sortPosFast {α} (l : List (Pos × α)) : List (Pos × α) := l.mergeSort posLE" \
  "def sortPosFast {α} (l : List (Pos × α)) : List (Pos × α) := l.mergeSort fun p q => p.1.cmp q.1 == .lt"

## What a read costs

# inRange_unbounded is false: a list with no lower bound starts nowhere.
mutant "a range with no lower bound that holds nothing" engine.core.Query engine/core/Query.lean:inRange_unbounded engine/core/Query.lean \
  "  (match q.after with | some a => p.cmp a == .gt | none => true) &&" \
  "  (match q.after with | some a => p.cmp a == .gt | none => false) &&"
# readPlan_cost is false: every read counts its whole range, however long.
mutant "a read that walks its whole list to count it" engine.core.Query engine/core/Query.lean:readPlan_cost engine/core/Query.lean \
  "  inRange := if (q.after.isNone && q.before.isNone && others.isEmpty) || (splitOf q others).isSome then none" \
  "  inRange := if (splitOf q others).isSome then none"
# readPlan_cost is false: the rows statement has no LIMIT.
mutant "a read that ignores its limit" engine.core.Query engine/core/Query.lean:readPlan_cost engine/core/Query.lean \
  "  rows := if q.limit = some 0 then none else some (.rows k others q.after q.before q.desc q.limit)" \
  "  rows := if q.limit = some 0 then none else some (.rows k others q.after q.before q.desc none)"
# readPlan_cost_range is false: a range's count ignores its cap.
mutant "a range's count that ignores its cap" engine.core.Query engine/core/Query.lean:readPlan_cost_range engine/core/Query.lean \
  "    else some (.count k others q.after q.before q.cap)" "    else some (.count k others q.after q.before 0)"
# readPlan_cost_le is false (its per-statement bound, plan_stmt_cost): a
# conjunction checks each other key twice a row.
mutant "a conjunction that checks each key twice" engine.core.Query engine/core/Query.lean:plan_stmt_cost engine/core/Query.lean \
  "  rows := if q.limit = some 0 then none else some (.rows k others q.after q.before q.desc q.limit)" \
  "  rows := if q.limit = some 0 then none else some (.rows k (others ++ others) q.after q.before q.desc q.limit)"
# listPlan_split is false: a one-bound count never splits, so it always
# walks the newer side whole.
mutant "a count that always walks the newer side" engine.core.Query engine/core/Query.lean:listPlan_split \
  engine/core/Query.lean \
  "  split := (splitOf q others).map fun (p, above) => (k, p, above)" "  split := none"
# splitWalk_steps (so splitWalk_cost) is false: the walk never tries the
# rest, only the range, doubling.
mutant "a split count that never walks the rest" engine.core.Query engine/core/Query.lean:splitWalk_steps \
  engine/core/Query.lean \
  "    let b ← cnt false (some L)
    if b < L then return (total - b, true)
" ""
# splitWalk_exact is false: the rest's count is returned as the range's.
mutant "a split count that answers with the rest" engine.core.Query engine/core/Query.lean:splitWalk_exact \
  engine/core/Query.lean "    if b < L then return (total - b, true)" "    if b < L then return (b, true)"
# splitWalk_cost_max is false: past the last doubling the range is walked
# whole, however long.
mutant "a walk with no ceiling" engine.core.Query engine/core/Query.lean:splitWalk_cost_max \
  engine/core/Query.lean "  | 0, _, lo => do
    let e ← est
    pure (max lo (min e (total - lo)), false)" "  | 0, _, _ => do
    let a ← cnt true none
    pure (a, true)"
# splitWalk_interval is false: the estimate is answered as it comes.
mutant "an unclamped estimate" engine.core.Query engine/core/Query.lean:splitWalk_interval \
  engine/core/Query.lean "    pure (max lo (min e (total - lo)), false)" "    pure (e, false)"
# pickMin_le is false: a conjunction walks its largest conjunct.
mutant "a conjunction that walks its largest key" engine.core.Query engine/core/Query.lean:pickMin_le engine/core/Query.lean \
  "  | best, kn :: rest => pickMin (if kn.2 < best.2 then kn else best) rest" \
  "  | best, kn :: rest => pickMin (if best.2 < kn.2 then kn else best) rest"

## The device as state

# secret_derives is false (its validator form, check_secret): the validator
# checks the public key only.
mutant "a secret op whose X25519 secret is not checked" ops.community.Laws ops/community/Laws.lean:check_secret ops/community/Facts.lean \
  "    if C.pub seed = pk ∧ C.keys seed = (sk, e, x) then" "    if C.pub seed = pk then"
# ofSeed_ed25519 is false: the derived X25519 secret is not the crypto's.
mutant "a device whose X25519 secret is converted from its public key" ops.community.Compose ops/community/Compose.lean:ofSeed_ed25519 \
  ops/community/Compose.lean "  ⟨kp.1, ks.1, ks.2.1, ks.2.2, seed⟩" "  ⟨kp.1, ks.1, ks.2.1, Crypto.staticOf kp.1, seed⟩"
# NoDerive: an intent that takes a seed and derives the device from it.
mutant "a seed-taking intent" ops.community.NoDerive ops/community/NoDerive.lean:#intents_derive_no_keys ops/community/Intents.lean \
  "/-! ## Laws -/" "def sendFromSeed (c myAdm : Id) (seed k nonce text : ByteArray) (now : Nat) : View Fact Write :=
  send c myAdm (Device.ofSeed seed) k nonce text now

/-! ## Laws -/"
# NoDerive: unwrap converts the signing secret on every run again.
mutant "unwrap that derives its X25519 secret" ops.community.NoDerive ops/community/NoDerive.lean:#intents_derive_no_keys ops/community/Intents.lean \
  "    match unbox cryptoSeal d.xsk kid bx with" "    match unbox cryptoSeal (Crypto.staticOf d.sk) kid bx with"
# NoDerive: the app's communities re-derive each device they read.
mutant "an Accepted read that derives each device again" ops.community.NoDerive ops/community/NoDerive.lean:#intents_derive_no_keys \
  ops/community/membership/AcceptedView.lean \
  "    let some dev := dev | continue" "    let some dev := dev.map (fun d => Device.ofSeed d.seed) | continue"
echo "all mutants refused, each by its law"
