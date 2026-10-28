#!/bin/sh
# Builds the network probe on the Mac, from the tree ship.sh stages
# (probe/ir: NetProbe's closure as C): its objects into libleanprobe.a
# beside Lean's runtime for the SDK (leanrt.sh, if not built yet), then the
# NetProbe target of the project (project.yml) around probe_ios.m. Prints
# the .app's path last.
#
#   build_probe.sh stage_dir build_dir sim|device
#
# device signs as build_ios.sh does (the quiet-build keychain, $IOS_PROFILE);
# with IOS_MULTICAST=1 it also asks for the multicast entitlement
# (multicast.entitlements), which the profile must carry.
set -eu
st=$(cd "$1" && pwd); b=$(cd "$2" && pwd); kind=${3:-sim}
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
xcodegen=${XCODEGEN:-$HOME/quiet-e2e/xcodegen/bin/xcodegen}
case $kind in
  sim)    sdk=iphonesimulator; tgt=arm64-apple-ios17.0-simulator ;;
  device) sdk=iphoneos;        tgt=arm64-apple-ios17.0 ;;
  *) echo "usage: build_probe.sh stage_dir build_dir sim|device"; exit 2 ;;
esac
rt=$b/leanrt
[ -f "$rt/$sdk/libInit.a" ] || "$st/ios/leanrt.sh" "$st" "$rt" "$sdk" >/dev/null
o=$b/probe-$sdk
rm -rf "$o"; mkdir -p "$o"
cc="xcrun -sdk $sdk clang --target=$tgt"
for c in "$st"/probe/ir/*.c; do
  case $(basename "$c") in
    NetProbe.c) echo "$c|-Dmain=lean_app_main" ;;
    *) echo "$c|" ;;
  esac
done | tr '\n' '\0' | xargs -0 -P "$(sysctl -n hw.ncpu)" -n 1 sh -c '
  src=${0%%|*}; flags=${0#*|}
  '"$cc"' -O2 -w -I'"$st"'/lean/include $flags -c "$src" -o '"$o"'/$(basename "${src%.c}").o || exit 255'
rm -f "$rt/$sdk/libleanprobe.a"
xcrun -sdk $sdk ar rcs "$rt/$sdk/libleanprobe.a" "$o"/*.o

export LEANQUIET_ST="$st" LEANQUIET_LIBS="$rt/$sdk"
(cd "$st/ios" && "$xcodegen" generate --spec project.yml --project . --quiet)
dd=$b/dd
case $kind in
  sim)
    xcodebuild -project "$st/ios/LeanQuiet.xcodeproj" -scheme NetProbe -configuration Release \
      -sdk iphonesimulator -destination 'generic/platform=iOS Simulator' -derivedDataPath "$dd" \
      ARCHS=arm64 CODE_SIGN_IDENTITY=- CODE_SIGN_STYLE=Manual DEVELOPMENT_TEAM= -quiet build
    echo "$dd/Build/Products/Release-iphonesimulator/NetProbe.app" ;;
  device)
    kc=$HOME/Library/Keychains/quiet-build.keychain-db
    security unlock-keychain -p "$(cat "$HOME/quiet-e2e/.build-keychain-pass")" "$kc"
    ent=
    if [ "${IOS_MULTICAST:-0}" = 1 ]; then
      ent="CODE_SIGN_ENTITLEMENTS=$st/ios/probe/multicast.entitlements"
    fi
    # shellcheck disable=SC2086
    xcodebuild -project "$st/ios/LeanQuiet.xcodeproj" -scheme NetProbe -configuration Release \
      -sdk iphoneos -destination 'generic/platform=iOS' -derivedDataPath "$dd" \
      CODE_SIGN_STYLE=Manual CODE_SIGN_IDENTITY="Apple Development" \
      PROVISIONING_PROFILE_SPECIFIER="${IOS_PROFILE:-ce2632b9-021a-472c-96ab-67dba7d10036}" \
      $ent -quiet build
    echo "$dd/Build/Products/Release-iphoneos/NetProbe.app" ;;
esac
