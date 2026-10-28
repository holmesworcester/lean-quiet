#!/usr/bin/env bash
# Builds the Lean chat app into an Android APK: lake emits the app's C
# (Main.lean and the Chat modules), NDK clang compiles it with the twin
# (activity.c, scroll.c, layer.c, lean_android.c) against Lean's runtime
# and Init for Android (android/leanrt/build.sh) into libleanapp.so per
# ABI, and aapt2/zipalign/apksigner package it (no Gradle). assets/ (the
# photos) ships in the APK; activity.c copies it into the app's data
# directory, the app's cwd, at startup.
#
# usage: build_apk.sh out.apk package label [abi...]
#   abi: arm64-v8a (default) and/or x86_64 (the emulator)
# env: ANDROID_SDK (default ~/android-sdk), LEAN_SRC (Lean's source at the
#   toolchain's version) and UV_SRC (libuv's), when the runtime is not built
set -euo pipefail
[ $# -ge 3 ] || { sed -n 2,13p "$0"; exit 2; }
out=$(realpath -m "$1"); pkg=$2; label=$3; shift 3
abis=("${@:-arm64-v8a}")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
sdk=${ANDROID_SDK:-$HOME/android-sdk}
ndk=$(ls -d "$sdk"/ndk/* | sort -V | tail -1)
cc=$ndk/toolchains/llvm/prebuilt/linux-x86_64/bin/clang
bt=$(ls -d "$sdk"/build-tools/* | sort -V | tail -1)
jar=$(ls -d "$sdk"/platforms/android-* | sort -V | tail -1)/android.jar
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
rt=$root/out/leanrt
work=$(mktemp -d "${TMPDIR:-/tmp}/lean-apk.XXXXXX")
trap 'rm -rf "$work"' EXIT

(cd "$root" && "$ELAN_HOME/bin/lake" build Main >/dev/null)
ir=$root/.lake/build/ir
for abi in "${abis[@]}"; do
  case $abi in
    arm64-v8a) tgt=aarch64-linux-android29 ;;
    x86_64)    tgt=x86_64-linux-android29 ;;
    *) echo "unknown abi $abi" >&2; exit 2 ;;
  esac
  [ -f "$rt/$abi/libInit.a" ] || "$root/android/leanrt/build.sh" "${LEAN_SRC:?LEAN_SRC}" \
    "${UV_SRC:?UV_SRC}" "$rt" "$abi"
  o=$work/$abi
  mkdir -p "$o" "$work/apk/lib/$abi"
  flags=(--target=$tgt -O3 -fPIC -ffunction-sections -fdata-sections -w -I"$rt/include")
  for c in "$ir"/Chat/*.c "$ir"/Chat.c; do
    "$cc" "${flags[@]}" -c "$c" -o "$o/$(basename "${c%.c}")_$(basename "$(dirname "$c")").o" &
  done
  "$cc" "${flags[@]}" -Dmain=lean_app_main -c "$ir/Main.c" -o "$o/Main.o" &
  wait
  for c in activity scroll layer lean_android; do
    "$cc" --target=$tgt -std=c11 -O3 -fPIC -I"$here" -I"$rt/include" -c "$here/$c.c" -o "$o/twin_$c.o"
  done
  "$cc" --target=$tgt -O3 -fPIC -c "$root/android/leanrt/notag.c" -o "$o/twin_notag.o"
  "$cc++" --target=$tgt -fPIC -shared -Wl,-z,max-page-size=16384 -Wl,--no-undefined -Wl,--gc-sections \
    "$o"/*.o -L"$rt/$abi" -Wl,--start-group -lInit -lleanrt -luv -Wl,--end-group \
    -static-libstdc++ -landroid -llog -lm -ldl \
    -o "$work/apk/lib/$abi/libleanapp.so"
done
sed -e "s/@PACKAGE@/$pkg/" -e "s/@LABEL@/$label/" \
  "$here/AndroidManifest.xml.in" > "$work/AndroidManifest.xml"
mkdir -p "$work/assets/assets"
cp "$root"/assets/[0-5].qoi "$work/assets/assets/"
"$bt/aapt2" link --debug-mode --manifest "$work/AndroidManifest.xml" -I "$jar" \
  -A "$work/assets" -o "$work/base.apk"
(cd "$work/apk" && zip -qr "$work/base.apk" lib)
"$bt/zipalign" -P 16 -f 4 "$work/base.apk" "$work/aligned.apk"
ks=$here/debug.keystore
[ -f "$ks" ] || keytool -genkeypair -keystore "$ks" -storepass android \
  -keypass android -alias lean -keyalg RSA -keysize 2048 -validity 10000 \
  -dname "CN=Lean debug" >/dev/null 2>&1
"$bt/apksigner" sign --ks "$ks" --ks-pass pass:android --ks-key-alias lean \
  --out "$out" "$work/aligned.apk"
echo "built $out (${abis[*]})"
