#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ ${LQ_ENDPOINT_SCOPE:-0} != 1 ]]; then
  exec systemd-run --user --scope -p MemoryMax=48G -p MemorySwapMax=0 \
    env LQ_ENDPOINT_SCOPE=1 ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp \
    PATH=/mnt/storage/elan/bin:"$PATH" bash tests/endpoints/tailnet.sh "$@"
fi
out=out/endpoints/tailnet-$(date +%s); mkdir -p "$out"
tailscale status >"$out/status.log"
# The authorized Linux test node only. No configuration/service changes.
node=clean-quiet-test
ssh -o BatchMode=yes -o ConnectTimeout=8 "$node" 'id; uname -sm; ss -ltn' >"$out/preflight.log" 2>&1 || {
  echo "clean-quiet-test unavailable; preflight retained in $out"; exit 1;
}
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
lake build endpoint_network >"$out/build.log" 2>&1
remote=$(ssh -o BatchMode=yes "$node" 'mktemp -d /tmp/leanquiet-endpoints.XXXXXX')
[[ "$remote" =~ ^/tmp/leanquiet-endpoints\.[[:alnum:]]+$ ]] || exit 1
printf '%s\n' "$remote" >"$out/remote-dir"
scp .lake/build/bin/endpoint_network "$node:$remote/endpoint_network" >"$out/copy.log" 2>&1
peer_ip=100.110.168.19
local_ip=100.67.2.56
pids=()
cleanup() {
  for pid in "${pids[@]}"; do kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; done
  ssh -o BatchMode=yes -o ConnectTimeout=5 "$node" "if test -f '$remote/pid'; then pid=\$(cat '$remote/pid'); case \$pid in ''|*[!0-9]*) exit 1;; esac; kill \"\$pid\" 2>/dev/null || true; fi" || true
  echo "Artifacts retained: $out and $node:$remote"
}
trap cleanup EXIT
# Reserve an unused port on each host; refuse to bind an existing service.
remote_port=$(ssh "$node" "python3 -c 'import socket;s=socket.socket();s.bind((\"0.0.0.0\",0));print(s.getsockname()[1])'")
local_port=$(python3 -c 'import socket;s=socket.socket();s.bind(("0.0.0.0",0));print(s.getsockname()[1])')
[[ "$remote_port" =~ ^[0-9]+$ && "$local_port" =~ ^[0-9]+$ ]] || exit 1
ssh "$node" "cd '$remote' && echo \$\$ >pid && exec ./endpoint_network B B.db '$remote_port' tailnet '$peer_ip:$remote_port' 75 '$local_ip'" >"$out/remote.log" 2>&1 & pids+=($!)
.lake/build/bin/endpoint_network A "$out/A.db" "$local_port" tailnet "$local_ip:$local_port" 75 "$peer_ip" >"$out/desktop.log" 2>&1 & pids+=($!)
for pid in "${pids[@]}"; do wait "$pid"; done
pids=()
grep -q 'PASS A single stable session' "$out/desktop.log"
id=$(sed -n 's/.*single stable session \([^;]*\);.*/\1/p' "$out/desktop.log")
grep -q "PASS B single stable session $id;" "$out/remote.log"
echo 'PASS routed unicast DNS-SD over Tailscale to authenticated TCP and marker exchange'
