#!/usr/bin/env bash
# Builds the camera harness APK with no Gradle and no libraries beyond the
# Android SDK and NDK:
#
# 1. lake emits C for the Qr and Pic libraries (they import only Init,
#    which is in Lean's runtime for Android: android/leanrt/build.sh).
# 2. NDK clang compiles that C and the JNI seams (jni/qr_jni.c, the
#    scanner's; jni/pic_jni.c, the image tools') into
#    libleanqr.so per ABI, against libleanrt, libInit and libuv.
# 3. javac and d8 build ScanActivity; aapt2, zipalign and apksigner
#    package and sign it (a debug key).
#
# usage: build_apk.sh out.apk [abi...]   (abi: x86_64 default, arm64-v8a)
# env: ANDROID_SDK (default ~/android-sdk); LEANRT (default out/leanrt)
set -euo pipefail
out=$(realpath -m "$1"); shift
abis=("${@:-x86_64}")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
sdk=${ANDROID_SDK:-$HOME/android-sdk}
ndk=$(ls -d "$sdk"/ndk/* | sort -V | tail -1)
cc=$ndk/toolchains/llvm/prebuilt/linux-x86_64/bin/clang
bt=$(ls -d "$sdk"/build-tools/* | sort -V | tail -1)
jar=$(ls -d "$sdk"/platforms/android-* | sort -V | tail -1)/android.jar
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
rt=${LEANRT:-$root/out/leanrt}
[ -f "$rt/include/lean/lean.h" ] || { echo "no Lean runtime at $rt: mise run android:runtime" >&2; exit 2; }
work=$(mktemp -d "$TMPDIR/lean-qr-apk.XXXXXX")
trap 'rm -rf "$work"' EXIT

# 1. Lean to C: every module of the library
mods=$(cd "$root" && find Qr Pic -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort; echo Qr; echo Pic)
(cd "$root" && "$ELAN_HOME/bin/lake" build $(for m in $mods; do echo "+$m:c"; done) >/dev/null)
cfiles=()
for m in $mods; do cfiles+=("$root/.lake/build/ir/${m//./\/}.c"); done

# 2. Native code per ABI
for abi in "${abis[@]}"; do
  case $abi in
    arm64-v8a) tgt=aarch64-linux-android29 ;;
    x86_64)    tgt=x86_64-linux-android29 ;;
    *) echo "unknown abi $abi" >&2; exit 2 ;;
  esac
  [ -f "$rt/$abi/libInit.a" ] || { echo "no runtime for $abi in $rt" >&2; exit 2; }
  o=$work/$abi
  mkdir -p "$o" "$work/apk/lib/$abi"
  flags=(--target=$tgt -O3 -fPIC -ffunction-sections -fdata-sections -w -I"$rt/include")
  i=0
  pids=()
  for c in "${cfiles[@]}"; do
    i=$((i + 1))
    "$cc" "${flags[@]}" -c "$c" -o "$o/m$i.o" & pids+=($!)
  done
  for j in qr_jni pic_jni; do
    "$cc" --target=$tgt -std=c11 -O2 -fPIC -Wall -Werror -I"$rt/include" -c "$here/jni/$j.c" -o "$o/$j.o" &
    pids+=($!)
  done
  "$cc" --target=$tgt -O2 -fPIC -c "$root/android/leanrt/notag.c" -o "$o/notag.o" & pids+=($!)
  for p in "${pids[@]}"; do wait "$p"; done
  "$cc++" --target=$tgt -fPIC -shared -Wl,-z,max-page-size=16384 -Wl,--no-undefined -Wl,--gc-sections \
    "$o"/*.o -L"$rt/$abi" -Wl,--start-group -lInit -lleanrt -luv -Wl,--end-group \
    -static-libstdc++ -llog -lm -ldl \
    -o "$work/apk/lib/$abi/libleanqr.so"
done

# 3. Java, manifest, package, sign
mkdir -p "$work/classes" "$work/dex"
javac --release 17 -nowarn -classpath "$jar" -d "$work/classes" \
  $(find "$here/java" -name '*.java') 2>&1 | grep -v '^Note:' || true
"$bt/d8" --min-api 29 --lib "$jar" --output "$work/dex" $(find "$work/classes" -name '*.class')
sed -e "s/@PACKAGE@/com.holmes.leanqr/" -e "s/@LABEL@/Lean QR/" \
  "$here/AndroidManifest.xml.in" > "$work/AndroidManifest.xml"
"$bt/aapt2" link --debug-mode --manifest "$work/AndroidManifest.xml" -I "$jar" -o "$work/base.apk"
cp "$work/dex/classes.dex" "$work/apk/"
(cd "$work/apk" && zip -qr "$work/base.apk" lib classes.dex)
"$bt/zipalign" -P 16 -f 4 "$work/base.apk" "$work/aligned.apk"
ks=$root/android/app/debug.keystore
[ -f "$ks" ] || keytool -genkeypair -keystore "$ks" -storepass android \
  -keypass android -alias lean -keyalg RSA -keysize 2048 -validity 10000 \
  -dname "CN=Lean QR debug" >/dev/null 2>&1
"$bt/apksigner" sign --ks "$ks" --ks-pass pass:android --ks-key-alias lean \
  --out "$out" "$work/aligned.apk"
echo "built $out (${abis[*]})"
