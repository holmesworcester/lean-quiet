#!/usr/bin/env bash
# Unicast DNS-SD over Tailscale between this host and a second tailnet node
# that runs on this host, in its own network namespace with its own tailscaled
# (ephemeral: in-memory state). Packets between the two cross both nodes'
# WireGuard data planes; a plain same-host run would only test loopback
# (`ip route get <own 100.x>` is `local … dev lo`).
#
#   tests/endpoints/tailnet-local.sh up     namespace, NAT, tailscaled; prints the
#                                           login URL and waits for its approval
#   tests/endpoints/tailnet-local.sh test   the real test (both processes)
#   tests/endpoints/tailnet-local.sh down   stops tailscaled, removes every rule,
#                                           the namespace and its resolv.conf
#
# Needs passwordless sudo and the tailnet owner's approval of the login (or
# TS_AUTHKEY, an ephemeral auth key, for unattended runs). Logs: out/endpoints.
set -euo pipefail
cd "$(dirname "$0")/../.."
ns=lqts
sock=/run/lqts/tailscaled.sock
net=10.200.200
host_if=lqts-h
ns_if=lqts-n
hostname=desktop-lq-test
state=out/endpoints/tailnet-local
mkdir -p "$state"

ts() { sudo -n ip netns exec "$ns" /usr/bin/tailscale --socket="$sock" "$@"; }

rules=(
  "-t nat -A POSTROUTING -s $net.0/30 ! -o $host_if -j MASQUERADE"
  "-I FORWARD 1 -i $host_if -j ACCEPT"
  "-I FORWARD 1 -o $host_if -j ACCEPT"
  "-I INPUT 1 -i $host_if -j ACCEPT"
)
# The same rules, deleted.
unrules=(
  "-t nat -D POSTROUTING -s $net.0/30 ! -o $host_if -j MASQUERADE"
  "-D FORWARD -i $host_if -j ACCEPT"
  "-D FORWARD -o $host_if -j ACCEPT"
  "-D INPUT -i $host_if -j ACCEPT"
)

up() {
  if ! ip netns list | grep -qx "$ns\( .*\)\?"; then
    sudo -n ip netns add "$ns"
    sudo -n ip link add "$host_if" type veth peer name "$ns_if"
    sudo -n ip link set "$ns_if" netns "$ns"
    sudo -n ip addr add "$net.1/30" dev "$host_if"
    sudo -n ip link set "$host_if" up
    sudo -n ip netns exec "$ns" ip addr add "$net.2/30" dev "$ns_if"
    sudo -n ip netns exec "$ns" ip link set "$ns_if" up
    sudo -n ip netns exec "$ns" ip link set lo up
    sudo -n ip netns exec "$ns" ip route add default via "$net.1"
    for r in "${rules[@]}"; do sudo -n iptables $r; done
    sudo -n mkdir -p "/etc/netns/$ns"
    echo "nameserver 1.1.1.1" | sudo -n tee "/etc/netns/$ns/resolv.conf" >/dev/null
  fi
  if [[ ! -s "$state/tailscaled.pid" ]] || ! sudo -n kill -0 "$(cat "$state/tailscaled.pid")" 2>/dev/null; then
    sudo -n mkdir -p /run/lqts
    # The pid file holds tailscaled's own pid: the shell execs into it.
    sudo -n bash -c "echo \$\$ > '$PWD/$state/tailscaled.pid'; exec ip netns exec $ns /usr/sbin/tailscaled \
      --state=mem: --socket=$sock --statedir=/run/lqts --tun=tailscale1 --port=41642" \
      >"$state/tailscaled.log" 2>&1 &
    for _ in $(seq 50); do ts status >/dev/null 2>&1 && break; [[ -S "$sock" ]] && break; sleep 0.2; done
  fi
  if [[ "$(ts status --json 2>/dev/null | python3 -c 'import json,sys; print(json.load(sys.stdin).get("BackendState",""))' || true)" != Running ]]; then
    ts up --hostname="$hostname" --accept-dns=false --accept-routes=false ${TS_AUTHKEY:+--auth-key="$TS_AUTHKEY"} \
      >"$state/up.log" 2>&1 &
    for _ in $(seq 60); do grep -q 'https://' "$state/up.log" 2>/dev/null && break; sleep 0.5; done
    grep -o 'https://[^ ]*' "$state/up.log" | head -1 | sed 's/^/LOGIN URL: /' || true
    # Wait (up to 30 min) for the tailnet owner to approve the login.
    for _ in $(seq 1800); do
      [[ "$(ts status --json 2>/dev/null | python3 -c 'import json,sys; print(json.load(sys.stdin).get("BackendState",""))' || true)" == Running ]] && break
      sleep 1
    done
  fi
  ts ip -4 | head -1 > "$state/ip"
  echo "tailnet node $hostname up at $(cat "$state/ip")"
}

down() {
  if [[ -s "$state/tailscaled.pid" ]]; then
    ts logout >/dev/null 2>&1 || true
    sudo -n kill "$(cat "$state/tailscaled.pid")" 2>/dev/null || true
    rm -f "$state/tailscaled.pid"
  fi
  if ip netns list | grep -qx "$ns\( .*\)\?"; then
    for r in "${unrules[@]}"; do sudo -n iptables $r 2>/dev/null || true; done
    sudo -n ip link del "$host_if" 2>/dev/null || true
    sudo -n ip netns del "$ns"
    sudo -n rm -rf "/etc/netns/$ns"
  fi
  echo "tailnet node removed"
}

run_test() {
  local peer_ip local_ip out remote_port local_port pids=() dump
  peer_ip=$(cat "$state/ip")
  local_ip=$(tailscale ip -4 | head -1)
  out=out/endpoints/tailnet-local-$(date +%s); mkdir -p "$out"
  { tailscale status; echo; ts status; } >"$out/status.log" 2>&1
  { ip route get "$peer_ip"; ip route get "$local_ip"; } >"$out/routes.log"
  # The peer must be reached through tailscale0, not loopback or the veth.
  grep -q "dev tailscale0" <(ip route get "$peer_ip") || { echo "peer not routed via tailscale0"; exit 1; }
  if [[ ${LQ_ENDPOINT_SCOPE:-0} != 1 ]]; then
    systemd-run --user --scope --quiet -p MemoryMax=48G -p MemorySwapMax=0 \
      env LQ_ENDPOINT_SCOPE=1 ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp \
      PATH=/mnt/storage/elan/bin:"$PATH" lake build endpoint_network >"$out/build.log" 2>&1
  else
    lake build endpoint_network >"$out/build.log" 2>&1
  fi
  remote_port=$(sudo -n ip netns exec "$ns" python3 -c 'import socket;s=socket.socket();s.bind(("0.0.0.0",0));print(s.getsockname()[1])')
  local_port=$(python3 -c 'import socket;s=socket.socket();s.bind(("0.0.0.0",0));print(s.getsockname()[1])')
  # Every packet between the two on tailscale0 (host side), for the record.
  sudo -n bash -c "echo \$\$ > '$PWD/$out/tcpdump.pid'; exec tcpdump -i tailscale0 -nn -l host $peer_ip" \
    >"$out/tailscale0.txt" 2>"$out/tcpdump.log" &
  sleep 1
  cleanup() {
    for pid in "${pids[@]}"; do kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; done
    [[ -s "$out/tcpdump.pid" ]] && sudo -n kill "$(cat "$out/tcpdump.pid")" 2>/dev/null || true
    echo "Artifacts retained: $out"
  }
  trap cleanup EXIT
  sudo -n ip netns exec "$ns" sudo -n -u "$(id -un)" env PATH="$PATH" \
    .lake/build/bin/endpoint_network B "$out/B.db" "$remote_port" tailnet "$peer_ip:$remote_port" 75 "$local_ip" \
    >"$out/remote.log" 2>&1 & pids+=($!)
  .lake/build/bin/endpoint_network A "$out/A.db" "$local_port" tailnet "$local_ip:$local_port" 75 "$peer_ip" \
    >"$out/desktop.log" 2>&1 & pids+=($!)
  for pid in "${pids[@]}"; do wait "$pid"; done
  pids=()
  sleep 1
  [[ -s "$out/tcpdump.pid" ]] && sudo -n kill "$(cat "$out/tcpdump.pid")" 2>/dev/null || true
  rm -f "$out/tcpdump.pid"
  grep -q 'PASS A single stable session' "$out/desktop.log"
  id=$(sed -n 's/.*single stable session \([^;]*\);.*/\1/p' "$out/desktop.log")
  grep -q "PASS B single stable session $id;" "$out/remote.log"
  dns=$(grep -c "\.5353[: ]" "$out/tailscale0.txt" || true)
  tcp=$(grep -Ec "\.($remote_port|$local_port)[: ]" "$out/tailscale0.txt" || true)
  echo "tailscale0: $dns DNS-SD datagrams (UDP 5353), $tcp TCP segments on the session ports" | tee "$out/summary.txt"
  [[ "$dns" -gt 0 && "$tcp" -gt 0 ]] || { echo "no traffic seen on tailscale0"; exit 1; }
  echo 'PASS unicast DNS-SD over Tailscale to an authenticated TCP session and marker exchange'
}

case "${1:-all}" in
  up) up ;;
  test) run_test ;;
  down) down ;;
  all) up; trap down EXIT; run_test ;;
  *) echo "usage: $0 up|test|down|all" >&2; exit 2 ;;
esac
