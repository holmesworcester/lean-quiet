#!/bin/sh
# Builds lean-quiet for iOS on the Mac, from the tree ship.sh stages:
# Lean's runtime and Init (leanrt.sh, once per SDK), then the app's C (the
# app's modules, lean-engine's, Std's; Main.c's main renamed
# lean_app_main) with the SQLite/Ed25519 glue into libleanapp.a, each
# object rebuilt only when its source is newer; then xcodegen makes the
# project around quiet_ios.m and xcodebuild builds the app (and, for the
# Simulator, its UI test).
#
#   build_ios.sh stage_dir build_dir sim      # the Simulator; no signing
#   build_ios.sh stage_dir build_dir device   # an iPhone; signs with the
#       quiet-build keychain and the provisioning profile $IOS_PROFILE (a
#       UUID), default the team's wildcard development one (over SSH Xcode
#       cannot make profiles)
#
# Needs Xcode at $DEVELOPER_DIR (default Xcode 26.3; never xcode-select)
# and xcodegen ($XCODEGEN, default ~/quiet-e2e/xcodegen). Prints the built
# .app's path last.
set -eu
st=$(cd "$1" && pwd); mkdir -p "$2"; b=$(cd "$2" && pwd); kind=${3:-sim}
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
xcodegen=${XCODEGEN:-$HOME/quiet-e2e/xcodegen/bin/xcodegen}
case $kind in
  sim)    sdk=iphonesimulator; tgt=arm64-apple-ios17.0-simulator ;;
  device) sdk=iphoneos;        tgt=arm64-apple-ios17.0 ;;
  *) echo "usage: build_ios.sh stage_dir build_dir sim|device"; exit 2 ;;
esac
rt=$b/leanrt
[ -f "$rt/$sdk/libInit.a" ] || "$st/ios/leanrt.sh" "$st" "$rt" "$sdk" >/dev/null

# The app's C: one object per source, kept across builds and compiled again
# only when its source or flags change (a hash of both beside the object:
# sources can change to older files, as when a package is swapped, so
# their times would not tell).
o=$b/app-$sdk
mkdir -p "$o"
cc="xcrun -sdk $sdk clang --target=$tgt"
sqlite="-include $st/glue/quiet_config.h"
{
  for c in "$st"/ir/*.c; do
    case $(basename "$c") in
      Main.c) echo "$c|-O3 -w -I$st/lean/include -Dmain=lean_app_main" ;;
      *)      echo "$c|-O3 -w -I$st/lean/include" ;;
    esac
  done
  for c in "$st"/glue/glue.c "$st"/glue/crypto.c; do
    echo "$c|-O3 -w -std=c11 -I$st/lean/include -I$st/glue"
  done
  for c in "$st"/glue/sqlite3.c; do
    echo "$c|-O2 -w $sqlite -I$st/glue"
  done
} > "$b/sources-$sdk.txt"
# (one line, source|flags, per sh: NUL-separated, as macOS xargs has no
# -d and caps -I's command at 255 bytes; the line goes as $0)
tr '\n' '\0' < "$b/sources-$sdk.txt" | xargs -0 -P "$(sysctl -n hw.ncpu)" -n 1 sh -c '
  src=${0%%|*}; flags=${0#*|}
  obj='"$o"'/$(basename "${src%.c}").o
  h=$( (echo "$flags"; cat "$src" '"$st"'/glue/quiet_config.h '"$st"'/glue/sqlite3.h) | shasum | cut -c1-40)
  if [ ! -f "$obj" ] || [ "$(cat "$obj.sha" 2>/dev/null)" != "$h" ]; then
    '"$cc"' $flags -c "$src" -o "$obj.tmp" && mv "$obj.tmp" "$obj" && echo "$h" > "$obj.sha" || exit 255
  fi'
# only this build's objects (a module gone from the closure leaves none)
objs=$(sed 's/|.*//; s|.*/||; s|\.c$|.o|' "$b/sources-$sdk.txt" | sed "s|^|$o/|")
rm -f "$rt/$sdk/libleanapp.a"
# shellcheck disable=SC2086
xcrun -sdk $sdk ar rcs "$rt/$sdk/libleanapp.a" $objs
# The engine's Rust crypto, built for this SDK by ship.sh.
cp -p "$st/glue/rust/$sdk/liblq_crypto.a" "$rt/$sdk/liblq_crypto.a"

export LEANQUIET_ST="$st" LEANQUIET_LIBS="$rt/$sdk"
# The project goes beside the spec: xcodegen writes paths relative to the
# spec but marks them relative to the project, so the two must agree.
(cd "$st/ios" && "$xcodegen" generate --spec project.yml --project . --quiet)
dd=$b/dd
case $kind in
  sim)
    xcodebuild -project "$st/ios/LeanQuiet.xcodeproj" -scheme LeanQuiet -configuration Release \
      -sdk iphonesimulator -destination 'generic/platform=iOS Simulator' -derivedDataPath "$dd" \
      ARCHS=arm64 CODE_SIGN_IDENTITY=- CODE_SIGN_STYLE=Manual DEVELOPMENT_TEAM= -quiet build-for-testing
    echo "$dd/Build/Products/Release-iphonesimulator/LeanQuiet.app" ;;
  device)
    kc=$HOME/Library/Keychains/quiet-build.keychain-db
    security unlock-keychain -p "$(cat "$HOME/quiet-e2e/.build-keychain-pass")" "$kc"
    xcodebuild -project "$st/ios/LeanQuiet.xcodeproj" -scheme LeanQuiet -configuration Release \
      -sdk iphoneos -destination 'generic/platform=iOS' -derivedDataPath "$dd" \
      CODE_SIGN_STYLE=Manual CODE_SIGN_IDENTITY="Apple Development" \
      PROVISIONING_PROFILE_SPECIFIER="${IOS_PROFILE:-ce2632b9-021a-472c-96ab-67dba7d10036}" \
      -quiet build
    echo "$dd/Build/Products/Release-iphoneos/LeanQuiet.app" ;;
esac
