#!/usr/bin/env bash
# Builds a Lean app into an Android APK, with no Gradle:
#
# 1. lake emits C for the main module and every module it imports
#    (followed through `import` lines): this package's and lean-engine's
#    (.lake/build/ir of each package in lake-manifest.json); Std or Lean modules, which Android has no
#    prebuilt library for, are compiled to C from the toolchain's own
#    sources and .oleans (cached in out/stdc); Init is in libInit.
# 2. NDK clang compiles that C with the twin (activity.c, layer.c,
#    scroll.c, quiet_android.c, ctl.c), the glue (android/native: SQLite,
#    Ed25519, SHA-256 over third_party/) against Lean's runtime and Init
#    for Android (android/leanrt/build.sh) into libleanapp.so per ABI.
# 3. javac and d8 build the Java half (java/), and aapt2, zipalign and
#    apksigner package it with assets/.
#
# usage: build_apk.sh out.apk package label main-module [abi...]
#   abi: arm64-v8a (default) and/or x86_64 (the emulator)
# env: ANDROID_SDK (default ~/android-sdk); LEANRT, the built runtime
#   (default lean-chat's out/leanrt; android/leanrt/build.sh makes one)
set -euo pipefail
[ $# -ge 4 ] || { sed -n 2,21p "$0"; exit 2; }
out=$(realpath -m "$1"); pkg=$2; label=$3; main=$4; shift 4
abis=("${@:-arm64-v8a}")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
sdk=${ANDROID_SDK:-$HOME/android-sdk}
ndk=$(ls -d "$sdk"/ndk/* | sort -V | tail -1)
cc=$ndk/toolchains/llvm/prebuilt/linux-x86_64/bin/clang
bt=$(ls -d "$sdk"/build-tools/* | sort -V | tail -1)
plat=$(ls -d "$sdk"/platforms/android-* | sort -V | tail -1)
jar=$plat/android.jar
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
lake=$ELAN_HOME/bin/lake
rt=${LEANRT:-/mnt/storage/holmes-wt/lean-chat/out/leanrt}
[ -f "$rt/include/lean/lean.h" ] || { echo "no Lean runtime at $rt (set LEANRT)" >&2; exit 2; }
# every required package's directory (lean-engine, lean-qr, ...)
pkgs=$(cd "$root" && python3 -c 'import json, os; m=json.load(open("lake-manifest.json")); print(" ".join(os.path.realpath(p["dir"]) for p in m["packages"]))')
toolchain=$("$ELAN_HOME/bin/lean" --print-prefix)
work=$(mktemp -d "$TMPDIR/lean-apk.XXXXXX")
trap 'rm -rf "$work"' EXIT
cache=$root/out/cache
mkdir -p "$cache"

# 1. The module closure, and its C.
closure=$(python3 - "$main" "$toolchain/src/lean" "$root" $pkgs <<'PY'
import re, sys, os
main, core, roots = sys.argv[1], sys.argv[2], sys.argv[3:] + [sys.argv[2]]
seen, order = set(), []
def find(m):
    rel = m.replace('.', '/') + '.lean'
    for i, r in enumerate(roots):
        if os.path.exists(os.path.join(r, rel)):
            return i, os.path.join(r, rel)
    return None, None
def go(m):
    if m in seen or m == 'Init' or m.startswith('Init.'):
        return
    seen.add(m)
    i, path = find(m)
    if path is None:
        sys.exit(f'cannot find module {m}')
    for line in open(path, encoding='utf-8'):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', line)
        if mm:
            go(mm.group(1))
    order.append(f'{"core" if roots[i] == core else roots[i]} {m}')
go(main)
print('\n'.join(order))
PY
)
targets=$(echo "$closure" | awk '$1 != "core" {print "+" $2 ":c"}')
(cd "$root" && "$lake" build $targets >/dev/null)
cfiles=()
while read -r where mod; do
  rel=${mod//./\/}.c
  case $where in
    core)
      c=$root/out/stdc/$rel
      if [ ! -f "$c" ]; then
        mkdir -p "$(dirname "$c")"
        (cd "$toolchain/src/lean" && "$toolchain/bin/lean" -c "$c" "${mod//./\/}.lean")
      fi
      cfiles+=("$c") ;;
    *) cfiles+=("$where/.lake/build/ir/$rel") ;;
  esac
done <<< "$closure"
echo "modules: $(echo "$closure" | wc -l)"

# 2. Native code, per ABI.
for abi in "${abis[@]}"; do
  case $abi in
    arm64-v8a) tgt=aarch64-linux-android30 ;;
    x86_64)    tgt=x86_64-linux-android30 ;;
    *) echo "unknown abi $abi" >&2; exit 2 ;;
  esac
  [ -f "$rt/$abi/libInit.a" ] || { echo "no runtime for $abi in $rt" >&2; exit 2; }
  o=$work/$abi
  mkdir -p "$o" "$work/apk/lib/$abi" "$cache/$abi"
  flags=(--target=$tgt -O3 -fPIC -ffunction-sections -fdata-sections -w -I"$rt/include")
  i=0
  for c in "${cfiles[@]}"; do
    i=$((i + 1))
    if [ "$c" = "$root/.lake/build/ir/${main//./\/}.c" ]; then
      "$cc" "${flags[@]}" -Dmain=lean_app_main -c "$c" -o "$o/m$i.o" &
    else
      "$cc" "${flags[@]}" -c "$c" -o "$o/m$i.o" &
    fi
  done
  # Vendored C, compiled once per ABI (SQLite takes a while).
  tp=$root/third_party
  for src in "$tp/sqlite/sqlite3.c" "$tp/monocypher/monocypher.c" "$tp/monocypher/monocypher-ed25519.c"; do
    obj=$cache/$abi/$(basename "${src%.c}").o
    if [ ! -f "$obj" ] || [ "$src" -nt "$obj" ]; then
      "$cc" --target=$tgt -O2 -fPIC -ffunction-sections -fdata-sections -w \
        -DSQLITE_THREADSAFE=2 -DSQLITE_DQS=0 -DSQLITE_DEFAULT_MEMSTATUS=0 -DSQLITE_OMIT_LOAD_EXTENSION \
        -c "$src" -o "$obj" &
    fi
  done
  wait
  cp "$cache/$abi"/*.o "$o/"
  for c in activity scroll layer quiet_android ctl; do
    "$cc" --target=$tgt -std=c11 -O3 -fPIC -I"$here" -I"$rt/include" -c "$here/$c.c" -o "$o/twin_$c.o"
  done
  for c in glue_android sha256; do
    "$cc" --target=$tgt -std=c11 -O3 -fPIC -I"$rt/include" -I"$tp/sqlite" -I"$tp/monocypher" \
      -c "$root/android/native/$c.c" -o "$o/glue_$c.o"
  done
  "$cc" --target=$tgt -O3 -fPIC -c "$root/android/leanrt/notag.c" -o "$o/twin_notag.o"
  "$cc++" --target=$tgt -fPIC -shared -Wl,-z,max-page-size=16384 -Wl,--no-undefined -Wl,--gc-sections \
    "$o"/*.o -L"$rt/$abi" -Wl,--start-group -lInit -lleanrt -luv -Wl,--end-group \
    -static-libstdc++ -landroid -llog -lm -ldl \
    -o "$work/apk/lib/$abi/libleanapp.so"
done

# 3. The Java half, the manifest, assets; package and sign.
mkdir -p "$work/classes" "$work/dex"
javac --release 17 -nowarn -classpath "$jar" -d "$work/classes" \
  $(find "$here/java" -name '*.java') 2>&1 | grep -v '^Note:' || true
"$bt/d8" --min-api 30 --lib "$jar" --output "$work/dex" $(find "$work/classes" -name '*.class')
sed -e "s/@PACKAGE@/$pkg/" -e "s/@LABEL@/$label/" \
  "$here/AndroidManifest.xml.in" > "$work/AndroidManifest.xml"
mkdir -p "$work/assets/assets"
if [ -d "$root/assets" ]; then
  find "$root/assets" -maxdepth 1 -type f -exec cp {} "$work/assets/assets/" \;
fi
"$bt/aapt2" link --debug-mode --manifest "$work/AndroidManifest.xml" -I "$jar" \
  -A "$work/assets" -o "$work/base.apk"
cp "$work/dex/classes.dex" "$work/apk/"
(cd "$work/apk" && zip -qr "$work/base.apk" lib classes.dex)
"$bt/zipalign" -P 16 -f 4 "$work/base.apk" "$work/aligned.apk"
ks=$here/debug.keystore
[ -f "$ks" ] || keytool -genkeypair -keystore "$ks" -storepass android \
  -keypass android -alias lean -keyalg RSA -keysize 2048 -validity 10000 \
  -dname "CN=Lean debug" >/dev/null 2>&1
"$bt/apksigner" sign --ks "$ks" --ks-pass pass:android --ks-key-alias lean \
  --out "$out" "$work/aligned.apk"
echo "built $out (${abis[*]})"
