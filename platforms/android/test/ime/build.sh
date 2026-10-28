#!/usr/bin/env bash
# Builds the test IME (TestIme.java) into an APK, with no Gradle.
# usage: build.sh out.apk
set -euo pipefail
out=$(realpath -m "$1")
here=$(cd "$(dirname "$0")" && pwd)
sdk=${ANDROID_SDK:-$HOME/android-sdk}
bt=$(ls -d "$sdk"/build-tools/* | sort -V | tail -1)
jar=$(ls -d "$sdk"/platforms/android-* | sort -V | tail -1)/android.jar
work=$(mktemp -d "${TMPDIR:-/tmp}/testime.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/classes" "$work/dex" "$work/res"
"$bt/aapt2" compile --dir "$here/res" -o "$work/res.zip"
"$bt/aapt2" link --manifest "$here/AndroidManifest.xml" -I "$jar" "$work/res.zip" -o "$work/base.apk"
javac --release 17 -nowarn -classpath "$jar" -d "$work/classes" $(find "$here/java" -name '*.java') 2>&1 | grep -v '^Note:' || true
"$bt/d8" --min-api 30 --lib "$jar" --output "$work/dex" $(find "$work/classes" -name '*.class')
(cd "$work/dex" && zip -q "$work/base.apk" classes.dex)
"$bt/zipalign" -f 4 "$work/base.apk" "$work/aligned.apk"
ks=$here/../../twin/debug.keystore
"$bt/apksigner" sign --ks "$ks" --ks-pass pass:android --ks-key-alias lean --out "$out" "$work/aligned.apk"
echo "built $out"
