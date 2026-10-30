#!/usr/bin/env bash
# Reserve the shared Mac with mac-turn before building/running/testing.
set -euo pipefail
cd "$(dirname "$0")/../.."
mac=${MAC:?set MAC to the Mac, as user@host}
dir=${MAC_DIR:-lean-quiet-desktop-work}
art=out/macos
mkdir -p "$art"
export NATIVE_STAGE="$PWD/out/macos-stage" APP_MAIN=platforms.macos.Main APPLE_SDKS=macosx
platforms/ios/ship.sh stage > "$art/stage.log" 2>&1 || { tail -45 "$art/stage.log"; exit 1; }
cp -rp platforms/macos "$NATIVE_STAGE/macos"
if [ "${1:-build}" = stage ]; then exit; fi
ssh "$mac" "mkdir -p ~/$dir/stage ~/$dir/build ~/$dir/out"
rsync -a --delete "$NATIVE_STAGE/" "$mac:$dir/stage/"
ssh "$mac" "~/$dir/stage/macos/build.sh ~/$dir/stage ~/$dir/build" > "$art/build.log" 2>&1 || { tail -60 "$art/build.log"; exit 1; }
app=$(tail -1 "$art/build.log")
[[ $app = /*/LeanQuiet.app ]] || { echo 'No built app path' >&2; exit 1; }
if [ "${1:-build}" = build ]; then echo "$app"; exit; fi
if [ "$1" = e2e ]; then
  scp -q platforms/macos/{test.py,input.swift} "$mac:$dir/"
  ssh "$mac" "python3 ~/$dir/test.py '$app' ~/$dir/out" > "$art/e2e.log" 2>&1 || { cat "$art/e2e.log"; scp -qr "$mac:$dir/out/." "$art/" || true; exit 1; }
  scp -qr "$mac:$dir/out/." "$art/"
  cat "$art/e2e.log"
  python3 platforms/macos/check_scroll.py "$art"
else
  ssh "$mac" "open -n '$app'"
fi
