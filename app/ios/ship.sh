#!/usr/bin/env bash
# lean-quiet onto the iOS Simulator (or an iPhone) through the Mac, from
# here: lake emits C for Main's module closure (followed through `import`
# lines, as android/twin/build_apk.sh does: this package's modules and
# those of every package it requires (lake-manifest.json: lean-engine,
# lean-qr) from their .lake/build/ir, Std's compiled from the toolchain's
# sources into out/stdc), and this stages it with Init's C
# (tools/gen_init_c.sh), Lean's runtime source and headers, libuv's
# source, the SQLite/Ed25519 glue (android/native, third_party), the
# assets and ios/; copies the tree to the Mac and builds it there
# (build_ios.sh); then installs and launches it.
#
# usage: ship.sh stage    assemble out/ios-stage here only
#        ship.sh sim      build for the Simulator; install and launch it in
#                         the Mac's simulator of our own (sim.sh), with the
#                         chaos data (500 messages) if the database has
#                         none; a screenshot into out/ios-sim/
#        ship.sh e2e      sim, then the UI tests (UITests/) in it: the
#                         conversation (scroll, long press, keyboard,
#                         typing, send) and a pinned page (Paste: keyboard,
#                         typing a link, Continue); screenshots and the
#                         result bundle in out/ios-sim/
#        ship.sh mdns     the network probe (probe/) in the simulator:
#                         Lean's TCP both ways and lean-mdns both ways,
#                         checked by the Mac's dns-sd; out/ios-sim/probe-sim.txt
#        ship.sh mdns-device  the same on the iPhone $DEVICE (ask first;
#                         the first run needs a tap on the phone's local
#                         network prompt); out/ios-sim/probe-device.txt
#        ship.sh ctl CMD...   control commands to the app in the Simulator
#        ship.sh shot FILE    a screenshot of the Simulator, here
#        ship.sh device   build for an iPhone (signed), install nothing
#        ship.sh e2e-device   device, then on $DEVICE: installed, launched,
#                         driven over the Mac's Wi-Fi (chaos data, state,
#                         frames drawn); left running (ask before using
#                         the phone)
#        ship.sh run      device, then install on $DEVICE and launch (ask
#                         before using the phone)
#        ship.sh clean    delete the simulator and the Mac's work directory
# env: MAC (default you@your-mac), MAC_DIR (default
#   lean-quiet-ios-work, under the Mac's home; ship.sh owns it), DEVICE
#   (the phone's devicectl id, default the iPhone 16e), LEAN_SRC (Lean's
#   source at the toolchain's version), UV_SRC (libuv v1.51.0's), PORT (the
#   control channel's, default 7417), MESSAGES (chaos size, default 500),
#   MDNS (lean-mdns, built, for the probe), SECS (the probe's mDNS time),
#   IOS_MULTICAST=1 (the probe's device build asks for the multicast
#   entitlement), IOS_PROFILE (the provisioning profile's UUID).
# Take the Mac first: mac-turn wait <name> (see ~/.local/bin/mac-turn).
set -euo pipefail
what=${1:-sim}
root=$(cd "$(dirname "$0")/.." && pwd)
mac=${MAC:-you@your-mac}
dir=${MAC_DIR:-lean-quiet-ios-work}
device=${DEVICE:-5BD488FF-AD5C-5B43-BA3A-C61D1B5EE433}
lean_src=${LEAN_SRC:-/mnt/storage/holmes-wt/lean-src/lean4}
uv_src=${UV_SRC:-/mnt/storage/holmes-wt/lean-src/libuv}
port=${PORT:-7417}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
lake=$ELAN_HOME/bin/lake
T=$("$ELAN_HOME/bin/lean" --print-prefix)
st=$root/out/ios-stage
art=$root/out/ios-sim
dx="export DEVELOPER_DIR=/Applications/Xcode-26.3.0.app/Contents/Developer IOS_MULTICAST=${IOS_MULTICAST:-0}${IOS_PROFILE:+ IOS_PROFILE=$IOS_PROFILE};"

# The modules main imports, followed through `import` lines over the
# roots given (the last is the toolchain's sources), one "<i> <module>" a
# line, dependencies first: i is the root's index; Init is left out (its
# C is out/initc).
closure() {
  python3 - "$@" <<'PY'
import re, sys, os
main, roots = sys.argv[1], sys.argv[2:]
seen, order = set(), []
def find(m):
    rel = m.replace('.', '/') + '.lean'
    for i, r in enumerate(roots):
        if os.path.exists(os.path.join(r, rel)):
            return i, os.path.join(r, rel)
    return None, None
def go(m):
    if m in seen or m == 'Init' or m.startswith('Init.'):
        return
    seen.add(m)
    i, path = find(m)
    if path is None:
        sys.exit(f'cannot find module {m}')
    for line in open(path, encoding='utf-8'):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', line)
        if mm:
            go(mm.group(1))
    order.append(f'{i if i < len(roots) - 1 else "core"} {m}')
go(main)
print('\n'.join(order))
PY
}

# Std's C for a module, compiled from the toolchain's source once (out/stdc).
stdc() {
  local c=$root/out/stdc/${1//./\/}.c
  if [ ! -f "$c" ]; then
    mkdir -p "$(dirname "$c")"
    (cd "$T/src/lean" && "$T/bin/lean" -c "$c" "${1//./\/}.lean") >&2
  fi
  echo "$c"
}

# The twin's placement proofs (Placement.lean): they check, on standard
# axioms only, or nothing is staged.
proofs() {
  local out
  out=$(cd "$root" && "$lake" build Quiet.Geometry >/dev/null && "$lake" env lean ios/Placement.lean 2>&1) ||
    { echo "$out" >&2; echo "ios/Placement.lean does not check" >&2; exit 1; }
  if echo "$out" | grep -E "depends on axioms" |
      grep -vqE "\[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" ||
      echo "$out" | grep -qE "sorryAx|error"; then
    echo "$out" >&2; echo "ios/Placement.lean rests on more than the standard axioms" >&2; exit 1
  fi
}

stage() {
  proofs
  [ -f "$root/assets/font.bin" ] || "$root/tools/fetch_assets.sh"
  [ -d "$root/out/initc" ] || "$root/tools/gen_init_c.sh" "$root/out/initc"
  local closure targets roots engine
  # the engine's directory (its crypto: native/crypto.c and the Rust crate)
  engine=$(cd "$root" && python3 -c 'import json, os; m=json.load(open("lake-manifest.json")); print([os.path.realpath(p["dir"]) for p in m["packages"] if p["name"]=="engine"][0])')
  # this package, then every package it requires (lean-engine, lean-qr, ...)
  # shellcheck disable=SC2207
  roots=("$root" $(cd "$root" && python3 -c 'import json, os; m=json.load(open("lake-manifest.json")); print(" ".join(os.path.realpath(p["dir"]) for p in m["packages"]))'))
  closure=$(closure Main "${roots[@]}" "$T/src/lean")
  targets=$(echo "$closure" | awk '$1 != "core" {print "+" $2 ":c"}')
  # shellcheck disable=SC2086
  (cd "$root" && "$lake" build $targets >/dev/null)
  rm -rf "$st"
  mkdir -p "$st/ir" "$st/lean/include" "$st/lean/src" "$st/uv" "$st/glue"
  # Every copy keeps its source's time (cp -p), so the Mac rebuilds only
  # what changed.
  local where mod rel c
  while read -r where mod; do
    rel=${mod//./\/}.c
    case $where in
      core) c=$(stdc "$mod") ;;
      *) c=${roots[$where]}/.lake/build/ir/$rel ;;
    esac
    cp -p "$c" "$st/ir/$mod.c"
  done <<< "$closure"
  echo "modules: $(echo "$closure" | wc -l)"
  cp -rp "$root/out/initc" "$st/initc"
  cp -rp "$T/include/lean" "$st/lean/include/"
  sed 's/^#define LEAN_MIMALLOC$//' "$T/include/lean/config.h" > "$st/lean/include/lean/config.h"
  touch -r "$T/include/lean/config.h" "$st/lean/include/lean/config.h"
  echo '#define LEAN_GITHASH ""' > "$st/lean/include/githash.h"
  touch -r "$T/include/lean/config.h" "$st/lean/include/githash.h"
  cp -rp "$lean_src/src/runtime" "$lean_src/src/util" "$st/lean/src/"
  cp -rp "$uv_src/include" "$uv_src/src" "$st/uv/"
  cp -p "$root/android/native/glue_android.c" "$engine/native/crypto.c" \
    "$root"/third_party/sqlite/sqlite3.[ch] "$st/glue/"
  # The engine's Rust crypto, built here for the device and the
  # Simulator (pure Rust: the Mac only links it).
  local sdk rtgt
  for sdk in iphoneos iphonesimulator; do
    case $sdk in
      iphoneos) rtgt=aarch64-apple-ios ;;
      iphonesimulator) rtgt=aarch64-apple-ios-sim ;;
    esac
    (cd "$engine/native/crypto" && CARGO_TARGET_DIR="$root/out/cache/rust" cargo build --release --quiet --target "$rtgt")
    mkdir -p "$st/glue/rust/$sdk"
    cp -p "$root/out/cache/rust/$rtgt/release/liblq_crypto.a" "$st/glue/rust/$sdk/"
  done
  cp -rp "$root/assets" "$st/assets"
  cp -rp "$root/ios" "$st/ios"
  rm -rf "$st/ios/LeanQuiet.xcodeproj"
}

# The network probe (probe/NetProbe.lean over lean-mdns, $MDNS, built by
# lake there): its closure's C into the stage's probe/ir.
stage_probe() {
  local mdns closure where mod c
  mdns=${MDNS:-$root/../mdns}
  mkdir -p "$root/out/probe" "$st/probe/ir"
  LEAN_PATH=$mdns/.lake/build/lib/lean "$T/bin/lean" -c "$root/out/probe/NetProbe.c" \
    "$root/ios/probe/NetProbe.lean"
  closure=$(closure NetProbe "$root/ios/probe" "$mdns" "$T/src/lean")
  while read -r where mod; do
    case $where in
      0) c=$root/out/probe/NetProbe.c ;;
      1) c=$mdns/.lake/build/ir/${mod//./\/}.c ;;
      core) c=$(stdc "$mod") ;;
    esac
    cp -p "$c" "$st/probe/ir/$mod.c"
  done <<< "$closure"
  echo "probe modules: $(echo "$closure" | wc -l)"
}

# The staged tree to the Mac (its build/, outside the stage, stays).
push() {
  ssh "$mac" "mkdir -p ~/$dir/stage ~/$dir/build ~/$dir/out"
  rsync -a --delete "$st/" "$mac:$dir/stage/"
}

on_mac() {
  ssh "$mac" "$dx $*"
}

# A build on the Mac (its command line as on_mac's); its log in
# out/ios-build-<name>.log, the errors shown if it fails; prints the last
# line (the built .app's path).
mac_build() {
  local name=$1 log
  shift
  log=$root/out/ios-build-$name.log
  mkdir -p "$root/out"
  if ! on_mac "$*" > "$log" 2>&1 || ! tail -1 "$log" | grep -q '\.app$'; then
    grep -E 'error|FAILED|Undefined|ld: ' "$log" | grep -v '^/Applications/Xcode' | head -30 >&2
    echo "build failed: $log" >&2
    exit 1
  fi
  tail -1 "$log"
}

ctl() {
  ssh "$mac" "$dx python3 - -p $port $(printf "'%s' " "$@")" < "$root/ios/ctl.py"
}

sim() {
  stage
  push
  local app
  app=$(mac_build sim "~/$dir/stage/ios/build_ios.sh ~/$dir/stage ~/$dir/build sim")
  echo "built $app"
  on_mac "~/$dir/stage/ios/sim.sh ~/$dir install $app"
  on_mac "~/$dir/stage/ios/sim.sh ~/$dir launch $port" >/dev/null
  # a fresh install opens on Get started: found a community (its home),
  # fill it with chaos, open its conversation
  ctl ping "found general" "chaos ${MESSAGES:-500}" wait channel state
  sleep 3
  mkdir -p "$art"
  shot "$art/launch.png"
  echo "screenshot $art/launch.png"
}

shot() {
  on_mac "~/$dir/stage/ios/sim.sh ~/$dir shot ~/$dir/out/shot.png"
  scp -q "$mac:$dir/out/shot.png" "$1"
}

# The UI test in the simulator, on the app sim() built and seeded.
e2e() {
  sim
  local udid xcr
  udid=$(on_mac "~/$dir/stage/ios/sim.sh ~/$dir udid")
  xcr=$dir/out/e2e.xcresult
  on_mac "rm -rf ~/$xcr ~/$dir/out/shots; mkdir -p ~/$dir/out/shots"
  # the Paste page's targets, the composer's text rows and a link, from Lean
  # (test/Targets.lean), for the screen the twin reports
  local tw W dpi tg
  tw=$(ctl twin)
  W=$(echo "$tw" | sed -n 's/.* w \([0-9]*\) dpi \([0-9]*\).*/\1/p')
  dpi=$(echo "$tw" | sed -n 's/.* w \([0-9]*\) dpi \([0-9]*\).*/\2/p')
  tg=$(cd "$root" && "$lake" build Quiet.Pages Quiet.Composer Community >/dev/null &&
    "$lake" env lean --run ios/test/Targets.lean "$W" "$dpi")
  local field cont comp link
  field=$(echo "$tg" | sed -n 's/^field //p'); cont=$(echo "$tg" | sed -n 's/^continue //p')
  comp=$(echo "$tg" | sed -n 's/^composer //p'); link=$(echo "$tg" | sed -n 's/^link //p')
  [ -n "$field" ] && [ -n "$cont" ] && [ -n "$comp" ] && [ -n "$link" ] || { echo "no targets: $tg"; exit 1; }
  local ok=0
  on_mac "cd ~/$dir/stage/ios && TEST_RUNNER_LEANQUIET_CTL_PORT=$port \
    TEST_RUNNER_LEANQUIET_SHOTS=\$HOME/$dir/out/shots TEST_RUNNER_LEANQUIET_FIELD='$field' \
    TEST_RUNNER_LEANQUIET_CONTINUE='$cont' TEST_RUNNER_LEANQUIET_COMPOSER='$comp' \
    TEST_RUNNER_LEANQUIET_LINK='$link' xcodebuild test-without-building \
    -project LeanQuiet.xcodeproj -scheme LeanQuiet -configuration Release \
    -destination 'platform=iOS Simulator,id=$udid' -derivedDataPath ~/$dir/build/dd \
    -resultBundlePath ~/$xcr ARCHS=arm64 2>&1" > "$art/e2e.log" || ok=$?
  grep "pinned:" "$art/e2e.log" | sed 's/^.*pinned:/pinned:/' || true
  grep -Eq '\*\* TEST (EXECUTE )?SUCCEEDED \*\*' "$art/e2e.log" || ok=1
  rm -rf "$art/shots"
  scp -q -r "$mac:$dir/out/shots" "$art/shots" || true
  scp -q "$mac:$dir/app.log" "$art/app.log" || true
  tail -15 "$art/e2e.log"
  ls "$art/shots" 2>/dev/null || true
  if [ "$ok" != 0 ]; then
    echo "FAIL: the UI test failed (log $art/e2e.log, app log $art/app.log, result ~/$xcr on the Mac)"
    exit 1
  fi
  echo PASS
}

# The network probe (probe/), in the simulator (sim) or on $DEVICE
# (device), with the Mac as its peer (probe/probe_mac.sh): Lean's TCP out
# and in, and lean-mdns both ways (the app logs the Mac's `dns-sd -R
# probe`; the Mac's dns-sd lists and resolves the app's announcement). The
# report in out/ios-sim/probe-<kind>.txt; fails on any `fail` line.
probe() {
  local kind=$1 app
  stage
  stage_probe
  push
  app=$(mac_build "probe-$kind" "~/$dir/stage/ios/probe/build_probe.sh ~/$dir/stage ~/$dir/build $kind")
  echo "built $app"
  mkdir -p "$art"
  on_mac "~/$dir/stage/ios/probe/probe_mac.sh ~/$dir $app $kind $((port + 10)) ${SECS:-15} $device" \
    > "$art/probe-$kind.txt"
  cat "$art/probe-$kind.txt"
  if grep -q '^RESULT .*: FAIL' "$art/probe-$kind.txt" || ! grep -q '^RESULT' "$art/probe-$kind.txt"; then
    echo "FAIL: see $art/probe-$kind.txt"
    exit 1
  fi
  echo PASS
}

device() {
  stage
  push
  app=$(mac_build device "~/$dir/stage/ios/build_ios.sh ~/$dir/stage ~/$dir/build device")
  echo "built $app"
}

# The app end to end on the iPhone (device_mac.sh): installed, launched,
# driven over the Mac's Wi-Fi through the control channel; its console in
# out/ios-device/console.txt. Left running on the phone.
e2e_device() {
  device
  local ok=0
  mkdir -p "$root/out/ios-device"
  on_mac "~/$dir/stage/ios/device_mac.sh ~/$dir $app $device $port ${MESSAGES:-500}" \
    | tee "$root/out/ios-device/e2e.txt" || ok=$?
  scp -q "$mac:$dir/out/device-console.txt" "$root/out/ios-device/console.txt" || true
  [ "$ok" = 0 ] && tail -1 "$root/out/ios-device/e2e.txt" | grep -q PASS
}

case $what in
  stage) stage ;;
  sim) sim ;;
  e2e) e2e ;;
  mdns) probe sim ;;
  mdns-device) probe device ;;
  ctl) shift; ctl "$@" ;;
  shot) shot "${2:?file}" ;;
  device) device ;;
  e2e-device) e2e_device ;;
  run)
    device
    on_mac "xcrun devicectl device install app --device $device $app" | tail -2
    on_mac "xcrun devicectl device process launch --device $device --terminate-existing local.leanquiet.app" | tail -2 ;;
  clean)
    on_mac "~/$dir/stage/ios/sim.sh ~/$dir delete" || true
    ssh "$mac" "rm -rf ~/$dir" ;;
  *) sed -n 2,47p "$0"; exit 2 ;;
esac
