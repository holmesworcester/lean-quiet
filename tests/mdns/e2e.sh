#!/usr/bin/env bash
# mDNS end to end on this machine's network: real multicast on 224.0.0.251:5353.
#   1. Lean announces, another Lean process browses and finds it.
#   2. Lean announces, avahi (the system's responder) resolves it.
#   3. avahi publishes, Lean browses and finds it.
# 2 and 3 need avahi-daemon and avahi-utils; without them they fail, not skip,
# unless MDNS_E2E_NO_AVAHI=1. Logs stay in out/mdns-e2e/ for a failed run.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build mdns_demo >/dev/null
demo=.lake/build/bin/mdns_demo
out=out/mdns-e2e; mkdir -p "$out"
tag="e2e-$$"
pids=()
cleanup() { for p in "${pids[@]}"; do kill "$p" 2>/dev/null || true; done; }
trap cleanup EXIT
fail() { echo "FAIL: $*"; exit 1; }

echo "1. Lean announces, Lean browses"
"$demo" announce "Lean A $tag" _leanmdns._udp 7001 12 >"$out/announce.log" 2>&1 & pids+=($!)
sleep 1
"$demo" browse _leanmdns._udp 6 >"$out/browse1.log" 2>&1
grep -q "^found Lean A $tag .* 7001 impl=lean-mdns " "$out/browse1.log" || { cat "$out/browse1.log"; fail "Lean did not find Lean"; }
echo "   ok: $(grep "Lean A $tag" "$out/browse1.log" | cut -c1-100)"

if [ "${MDNS_E2E_NO_AVAHI:-0}" = 1 ]; then echo "2, 3: not run (MDNS_E2E_NO_AVAHI=1)"; exit 0; fi
command -v avahi-browse >/dev/null && command -v avahi-publish >/dev/null || fail "avahi-utils missing"

echo "2. Lean announces, avahi resolves"
timeout 8 avahi-browse -rpt _leanmdns._udp >"$out/avahi-browse.log" 2>&1 || true
grep -q "^=;.*;IPv4;Lean\\\\032A\\\\032$tag;_leanmdns._udp;local;.*;7001;\"impl=lean-mdns\"" "$out/avahi-browse.log" \
  || { cat "$out/avahi-browse.log"; fail "avahi did not resolve Lean's service"; }
echo "   ok: $(grep '^=' "$out/avahi-browse.log" | grep "$tag" | head -1 | cut -c1-110)"

echo "3. avahi publishes, Lean browses"
avahi-publish -s "Avahi B $tag" _leanmdns._udp 7002 "impl=avahi" >"$out/avahi-publish.log" 2>&1 & pids+=($!)
sleep 2
"$demo" browse _leanmdns._udp 6 >"$out/browse3.log" 2>&1
grep -q "^found Avahi B $tag .* 7002 impl=avahi " "$out/browse3.log" || { cat "$out/browse3.log"; fail "Lean did not find avahi's service"; }
echo "   ok: $(grep "Avahi B $tag" "$out/browse3.log" | cut -c1-100)"
echo "e2e: all passed"
