#!/usr/bin/env bash
# The macOS release: the AppKit app (platforms/macos) built on the Mac,
# signed with a Developer ID Application identity (hardened runtime,
# secure timestamp), notarized, stapled and zipped for the join page.
# Gatekeeper then opens it on any Mac with no warning about the developer.
#
# usage: tools/release/macos.sh X.Y.Z   -> out/release/LeanQuiet-macos.zip
# env:
#   MAC             user@host of the Mac (reserve it first: mac-turn wait NAME)
#   SIGN_IDENTITY   "Developer ID Application: Name (TEAMID)" (not Quiet's team)
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
id=${SIGN_IDENTITY:?set SIGN_IDENTITY to a Developer ID Application identity}
[[ $id = "Developer ID Application: "* ]] || { echo "SIGN_IDENTITY must be a Developer ID Application identity" >&2; exit 2; }
[[ $id != *CTYKSWN9T4* ]] || { echo "that is Quiet's team; Lean Quiet signs with another" >&2; exit 2; }
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
zip=$(tail -1 out/macos/release.log)
scp -q "$mac:$zip" out/release/LeanQuiet-macos.zip
ssh "$mac" "rm -rf ~/$dir"
echo "release $v: out/release/LeanQuiet-macos.zip (notarized, stapled; $id)"
