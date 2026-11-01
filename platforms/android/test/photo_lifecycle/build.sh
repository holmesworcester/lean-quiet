#!/usr/bin/env bash
set -euo pipefail
out=$(realpath -m "${1:?output APK}")
here=$(cd "$(dirname "$0")" && pwd)
sdk=${ANDROID_SDK:-$HOME/android-sdk}
bt=$(ls -d "$sdk"/build-tools/* | sort -V | tail -1)
jar=$(ls -d "$sdk"/platforms/android-* | sort -V | tail -1)/android.jar
work=$(mktemp -d "${TMPDIR:-/mnt/storage/holmes-tmp}/photo-lifecycle-apk.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/classes" "$work/dex"
javac --release 17 -nowarn -classpath "$jar" -d "$work/classes" "$here/java/com/holmes/photolifecycle/PhotoLifecycleProbe.java"
"$bt/d8" --min-api 30 --lib "$jar" --output "$work/dex" $(rg --files "$work/classes" -g '*.class')
"$bt/aapt2" link --manifest "$here/AndroidManifest.xml" -I "$jar" -o "$work/base.apk"
(cd "$work/dex" && zip -q "$work/base.apk" classes.dex)
"$bt/zipalign" -f 4 "$work/base.apk" "$work/aligned.apk"
"$bt/apksigner" sign --ks "$here/../../twin/debug.keystore" --ks-pass pass:android --ks-key-alias lean --out "$out" "$work/aligned.apk"
