#!/usr/bin/env bash
# The macOS release: the AppKit app (platforms/macos) built on the Mac and
# zipped for the join page. With SIGN_IDENTITY, it is signed with that
# Developer ID Application identity (hardened runtime, secure timestamp),
# notarized and stapled, so Gatekeeper opens it on any Mac without a
# warning. Without one it is ad-hoc signed: the first launch needs
# System Settings > Privacy & Security > Open Anyway.
#
# usage: tools/release/macos.sh X.Y.Z   -> out/release/LeanQuiet-macos.zip
# env:
#   MAC             user@host of the Mac (reserve it first: mac-turn wait NAME)
#   SIGN_IDENTITY   "Developer ID Application: Name (TEAMID)" (not Quiet's team);
#                   unset: ad-hoc, not notarized
#   KEYCHAIN        on the Mac, the keychain holding that identity
#                   (default ~/Library/Keychains/lean-quiet-release.keychain-db);
#                   an SSH session cannot use the login keychain
#   KEYCHAIN_PASS   on the Mac, a 600 file with that keychain's password
#                   (default ~/.lean-quiet-release-keychain-pass)
#   NOTARY_PROFILE  the notarytool profile stored in that keychain
#                   (default lean-quiet-notary; made once with
#                   xcrun notarytool store-credentials, see docs/RELEASE.md)
#   BUNDLE_ID       default io.github.holmesworcester.leanquiet.mac
#   MAC_DIR         default lean-quiet-release-work (deleted at the end)
set -euo pipefail
cd "$(dirname "$0")/../.."
v=${1:?usage: macos.sh X.Y.Z}
[[ $v =~ ^([0-9]+)\.([0-9]+)\.([0-9]+)$ ]] || { echo "version is X.Y.Z" >&2; exit 2; }
build=$(( BASH_REMATCH[1] * 10000 + BASH_REMATCH[2] * 100 + BASH_REMATCH[3] ))
mac=${MAC:?set MAC=user@host}
id=${SIGN_IDENTITY:-}
if [ -n "$id" ]; then
  [[ $id = "Developer ID Application: "* ]] || { echo "SIGN_IDENTITY must be a Developer ID Application identity" >&2; exit 2; }
  [[ $id != *CTYKSWN9T4* ]] || { echo "that is Quiet's team; Lean Quiet signs with another" >&2; exit 2; }
fi
kc=${KEYCHAIN:-'~/Library/Keychains/lean-quiet-release.keychain-db'}
kcpass=${KEYCHAIN_PASS:-'~/.lean-quiet-release-keychain-pass'}
profile=${NOTARY_PROFILE:-lean-quiet-notary}
bundle=${BUNDLE_ID:-io.github.holmesworcester.leanquiet.mac}
dir=${MAC_DIR:-lean-quiet-release-work}
mkdir -p out/release out/macos
platforms/macos/ship.sh stage > out/macos/release-stage.log 2>&1 || { tail -40 out/macos/release-stage.log; exit 1; }
ssh "$mac" "rm -rf ~/$dir && mkdir -p ~/$dir/stage ~/$dir/build"
rsync -a --delete out/macos-stage/ "$mac:$dir/stage/"
q() { printf '%q' "$1"; }
if [ -n "$id" ]; then
ssh "$mac" "set -euo pipefail
  security unlock-keychain -p \"\$(cat $kcpass)\" $kc
  export BUILD_NUMBER=$build VERSION=$v BUNDLE_ID=$bundle SIGN_IDENTITY=$(q "$id") SIGN_KEYCHAIN=$kc
  app=\$(~/$dir/stage/macos/build.sh ~/$dir/stage ~/$dir/build | tail -1)
  codesign --verify --strict --deep --verbose=2 \"\$app\"
  codesign -dv \"\$app\" 2>&1 | grep -E 'Authority=Developer ID Application|flags=.*runtime'
  cd \"\$(dirname \"\$app\")\"
  ditto -c -k --keepParent LeanQuiet.app LeanQuiet-macos.zip
  xcrun notarytool submit LeanQuiet-macos.zip --keychain-profile $profile --keychain $kc --wait --timeout 1h
  xcrun stapler staple LeanQuiet.app
  spctl -a -vvv -t exec LeanQuiet.app 2>&1 | grep -q 'source=Notarized Developer ID'
  rm LeanQuiet-macos.zip && ditto -c -k --keepParent LeanQuiet.app LeanQuiet-macos.zip
  echo \$PWD/LeanQuiet-macos.zip" > out/macos/release.log 2>&1 || { tail -40 out/macos/release.log; exit 1; }
else
ssh "$mac" "set -euo pipefail
  export BUILD_NUMBER=$build VERSION=$v BUNDLE_ID=$bundle
  app=\$(~/$dir/stage/macos/build.sh ~/$dir/stage ~/$dir/build | tail -1)
  codesign --verify --strict --deep --verbose=2 \"\$app\"
  /usr/libexec/PlistBuddy -c 'Print :CFBundleURLTypes:0:CFBundleURLSchemes:0' \"\$app/Contents/Info.plist\" | grep -qx leanquiet
  /usr/libexec/PlistBuddy -c 'Print :CFBundleShortVersionString' \"\$app/Contents/Info.plist\" | grep -qx $v
  cd \"\$(dirname \"\$app\")\"
  ditto -c -k --keepParent LeanQuiet.app LeanQuiet-macos.zip
  echo \$PWD/LeanQuiet-macos.zip" > out/macos/release.log 2>&1 || { tail -40 out/macos/release.log; exit 1; }
fi
zip=$(tail -1 out/macos/release.log)
scp -q "$mac:$zip" out/release/LeanQuiet-macos.zip
ssh "$mac" "rm -rf ~/$dir"
echo "release $v: out/release/LeanQuiet-macos.zip (${id:-ad-hoc signed, not notarized})"
