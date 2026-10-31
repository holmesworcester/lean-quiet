#!/usr/bin/env bash
# The Android release APK: non-debuggable, no control channel, signed with
# the release key (made once, kept outside the repo; every update must be
# signed with it), arm64-v8a for phones and x86_64 for emulators and
# Chromebooks. Checks what it built: the signer is the release key, the
# version, not debuggable, and the leanquiet://join/ filter.
#
# usage: tools/release/android.sh X.Y.Z   -> out/release/lean-quiet-android.apk
# env: LEANQUIET_RELEASE_KEYS (default ~/.config/lean-quiet/release):
#   android-release.jks and android-release.pass, alias lean-quiet
set -euo pipefail
cd "$(dirname "$0")/../.."
v=${1:?usage: android.sh X.Y.Z}
[[ $v =~ ^([0-9]+)\.([0-9]+)\.([0-9]+)$ ]] || { echo "version is X.Y.Z" >&2; exit 2; }
code=$(( BASH_REMATCH[1] * 10000 + BASH_REMATCH[2] * 100 + BASH_REMATCH[3] ))
keys=${LEANQUIET_RELEASE_KEYS:-$HOME/.config/lean-quiet/release}
ks=$keys/android-release.jks; pass=$keys/android-release.pass
[ -f "$ks" ] && [ -f "$pass" ] || { echo "no release key in $keys" >&2; exit 2; }
sdk=${ANDROID_SDK:-$HOME/android-sdk}
bt=$(ls -d "$sdk"/build-tools/* | sort -V | tail -1)
apk=out/release/lean-quiet-android.apk
mkdir -p out/release
[ -f "${LEANRT:-out/leanrt}/arm64-v8a/libInit.a" ] || mise run android:runtime
[ -f assets/font.bin ] || tools/fetch_assets.sh
RELEASE=1 VERSION_CODE=$code VERSION_NAME=$v KEYSTORE=$ks KEYSTORE_PASS_FILE=$pass KEY_ALIAS=lean-quiet \
  platforms/android/twin/build_apk.sh "$apk" com.holmes.leanquiet 'Lean Quiet' Main arm64-v8a x86_64

# What was built.
want=$(keytool -exportcert -keystore "$ks" -storepass:file "$pass" -alias lean-quiet 2>/dev/null | sha256sum | cut -d' ' -f1)
got=$("$bt/apksigner" verify --print-certs "$apk" | sed -n 's/^Signer #1 certificate SHA-256 digest: //p')
[ "$got" = "$want" ] || { echo "signed by $got, not the release key $want" >&2; exit 1; }
badging=$("$bt/aapt2" dump badging "$apk")
grep -q "package: name='com.holmes.leanquiet' versionCode='$code' versionName='$v'" <<<"$badging" || { echo "wrong version" >&2; exit 1; }
! grep -q "application-debuggable" <<<"$badging" || { echo "debuggable" >&2; exit 1; }
tree=$("$bt/aapt2" dump xmltree --file AndroidManifest.xml "$apk")
grep -q '"leanquiet"' <<<"$tree" && grep -q 'android:host.*"join"' <<<"$tree" || { echo "no leanquiet://join/ filter" >&2; exit 1; }
! grep -q '"quiet"' <<<"$tree" || { echo "still claims quiet://" >&2; exit 1; }
echo "release $v ($code): $apk, signer sha256 $got"
