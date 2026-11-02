#!/usr/bin/env bash
# The negative control of the make demo e2e (tests/make/demo_e2e.py): once
# Bob is in, his app restarts with --offline (no sockets), and Alice then
# types a message. The e2e must fail, at both checks that the message
# reached Bob (his state, and his screen against Alice's), and pass every
# check before them: what makes it pass is the network, nothing else.
# Artifacts: out/make/demo-negative/ (its log: e2e.log).
set -uo pipefail
top=$(cd "$(dirname "$0")/../.." && pwd)
cd "$top"
out=$top/out/make/demo-negative
mkdir -p "$out"
DEMO_E2E_OUT=$out python3 tests/make/demo_e2e.py --control offline > "$out.log" 2>&1
code=$?
mv "$out.log" "$out/e2e.log"
log=$out/e2e.log
fail() { echo "demo negative: $* (see $log)"; exit 1; }
[ "$code" = 1 ] || fail "the e2e exited $code with Bob offline, not 1"
grep -q "^ok   Bob, offline, opens #general again" "$log" || fail "the e2e failed before Bob was offline"
grep -q "^ok   Alice's message is in her conversation, sent" "$log" || fail "Alice's message was not sent"
grep -q "^FAIL Bob's state shows Alice's message (QUIET_STATE)" "$log" || fail "the state check did not fail"
grep -q "^FAIL Bob's screen shows Alice's message as Alice's does" "$log" || fail "the screen check did not fail"
grep -q "^ok   the screen check's control" "$log" || fail "the screen check's own control did not pass"
[ "$(grep -c '^FAIL' "$log")" = 2 ] || fail "other checks failed too"
echo "demo negative: with Bob offline, both checks that Alice's message reached him fail (state and screen)"
