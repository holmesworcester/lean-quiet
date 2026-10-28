#!/bin/sh
# The network probe, run from the Mac in the simulator (sim.sh's) or on an
# iPhone (devicectl), with the Mac as its peer:
# - harness.py answers its TCP steps (in the Simulator over the Mac's
#   loopback; on a phone over the Wi-Fi, the Mac's en0 address);
# - `dns-sd -R probe _leanquiet._udp local 7001` registers a service with
#   the Mac's own mDNS responder: the probe must log it found (multicast
#   into the app);
# - `dns-sd -B _leanquiet._udp` and, midway, `dns-sd -L <instance>` must
#   list and resolve the probe's own announcement (multicast out of it);
# - the same for the system's DNS-SD (dnssd.c, driven by Lean): the Mac must list
#   <instance>-sd, and the app must resolve the Mac's `probe`.
# The report: work_dir/out/probe.txt: the probe's log, the harness's, the
# Mac's checks, and three results (RESULT <name>: PASS|FAIL), each from the
# app's own verdict and the Mac's view: lean-mdns raw multicast; dns_sd
# register/browse/resolve with Lean's TCP to the address it resolved; TCP
# to the Mac and from it.
#
#   probe_mac.sh work_dir app sim|device port seconds [device_id]
set -eu
w=$1; app=$2; kind=$3; port=$4; secs=$5; dev=${6:-}
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
here=$(cd "$(dirname "$0")" && pwd)
out=$w/out
mkdir -p "$out"
rm -f "$out"/probe.txt "$out"/console.txt "$out"/browse.txt "$out"/lookup.txt "$out"/harness.txt
case $kind in
  sim)
    u=$("$here/../sim.sh" "$w" udid)
    xcrun simctl install "$u" "$app"
    # (the harness on every interface: dns_sd resolves the Mac's en0)
    inst=lean-ios-sim; bind=0.0.0.0; host=127.0.0.1; target=127.0.0.1 ;;
  device)
    xcrun devicectl device install app --device "$dev" "$app" >/dev/null
    inst=lean-ios-phone; bind=$(ipconfig getifaddr en0); host=$bind; target=@$out/console.txt ;;
  *) sed -n 2,15p "$0"; exit 2 ;;
esac
python3 "$here/harness.py" "$port" "$bind" "$target" > "$out/harness.txt" 2>&1 &
hp=$!
dns-sd -R probe _leanquiet._udp local 7001 > /dev/null 2>&1 &
rp=$!
dns-sd -B _leanquiet._udp local > "$out/browse.txt" 2>&1 &
bp=$!
sleep 1
if [ "$kind" = sim ]; then
  xcrun simctl launch --console --terminate-running-process "$u" local.leanquiet.netprobe \
    "$host" "$port" "$secs" "$inst" > "$out/console.txt" 2>&1 &
else
  xcrun devicectl device process launch --console --terminate-existing --device "$dev" \
    local.leanquiet.netprobe "$host" "$port" "$secs" "$inst" > "$out/console.txt" 2>&1 &
fi
pp=$!
sleep $((secs / 2 + 1))
dns-sd -L "$inst" _leanquiet._udp local > "$out/lookup.txt" 2>&1 &
lp=$!
sleep 4
{ kill "$lp"; wait "$lp"; } 2>/dev/null || true
# The probe ends by itself (every step is bounded); waited for at most
# its time and 90 s more.
n=0
while kill -0 "$pp" 2>/dev/null && [ $n -lt $((secs + 90)) ]; do
  sleep 1; n=$((n + 1))
done
kill "$pp" 2>/dev/null || true
kill "$rp" "$bp" "$hp" 2>/dev/null || true
wait 2>/dev/null || true
# (devicectl's console ends lines with CR LF)
tr -d '\r' < "$out/console.txt" > "$out/console.lf" && mv "$out/console.lf" "$out/console.txt"
{
  echo "== the harness (TCP peer, $bind:$port)"
  cat "$out/harness.txt"
  echo "== the Mac's mDNS responder"
  # (the instance ends the line: lean-ios-phone is not lean-ios-phone-sd)
  if tr -d '\r' < "$out/browse.txt" | grep -Eq "Add .* $inst *\$"; then
    echo "ok mac-browse: $(tr -d '\r' < "$out/browse.txt" | grep -E "Add .* $inst *\$" | head -1 | tr -s ' ')"
  else
    echo "fail mac-browse: dns-sd -B never listed $inst"
  fi
  if grep -q 'can be reached at' "$out/lookup.txt"; then
    echo "ok mac-lookup: $(grep 'can be reached at' "$out/lookup.txt" | head -1 | tr -s ' ')"
  else
    echo "fail mac-lookup: dns-sd -L did not resolve $inst"
  fi
  if tr -d '\r' < "$out/browse.txt" | grep -Eq "Add .* $inst-sd *\$"; then
    echo "ok mac-browse-dnssd: $(grep "Add.*$inst-sd" "$out/browse.txt" | head -1 | tr -s ' ')"
  else
    echo "fail mac-browse-dnssd: dns-sd -B never listed $inst-sd (the app's DNS-SD registration)"
  fi
  # the Mac's registration: port 7001 at the Mac's own address (a name
  # taken on the LAN already is renamed by the responder: "probe (2)")
  mine=$(ipconfig getifaddr en0)
  if grep -E "^ok mdns-found probe( \([0-9]+\))? .*port 7001 .* $mine( |\$)" "$out/console.txt" >/dev/null; then
    echo "ok app-found: the app logged the Mac's dns-sd -R registration (port 7001, $mine)"
  else
    echo "fail app-found: the probe never logged the Mac's 'probe' (dns-sd -R, port 7001, $mine)"
  fi
  if grep -E "^ok dnssd-found probe( \([0-9]+\))? .*port 7001 addr $mine" "$out/console.txt" >/dev/null; then
    echo "ok app-found-dnssd: the app's DNS-SD resolved the Mac's registration to $mine:7001"
  else
    echo "fail app-found-dnssd: the app's DNS-SD never resolved the Mac's 'probe' to $mine:7001"
  fi
} > "$out/checks.txt"
# The three results, each from the app's own verdict and the Mac's view.
res() {
  if grep -qF "result $1: ok" "$out/console.txt" && ! grep -Eq "^fail ($2)" "$out/checks.txt"; then
    echo "RESULT $1: PASS"
  else
    echo "RESULT $1: FAIL"
  fi
}
{
  echo "== the probe ($kind, $inst)"
  cat "$out/console.txt"
  sed -n '/^== the harness/,$p' "$out/checks.txt"
  echo "== results"
  res "lean-mdns raw multicast" "mac-browse:|mac-lookup|app-found:"
  res "dns_sd register/browse/resolve (+ Lean TCP to what it resolved)" "mac-browse-dnssd|app-found-dnssd"
  res "TCP to the Mac (out) and from it (in)" "NONE"
} > "$out/probe.txt"
cat "$out/probe.txt"
