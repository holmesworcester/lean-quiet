#!/bin/sh
# Lean's runtime and Init for Android: libleanrt.a, libInit.a and libuv.a
# per ABI. (Copied unchanged from lean-chat's android/leanrt.)
#
# The toolchain ships these for its host only, so this builds them from
# Lean's source (at the toolchain's version) and from Init's C, which
# tools/gen_init_c.sh emits with the toolchain itself (so they match the
# C our program is compiled to). Differences from the host build:
# - no mimalloc (Lean's own small-object allocator instead), no GMP
#   (Lean's own bignums);
# - OpenSSL left out: its glue compiles in the stub form the WebAssembly
#   build uses (LEAN_EMSCRIPTEN, that file only), as the app does no TLS;
# - libuv compiled from uv_src (its CMakeLists' Android source list,
#   without running its build), as Lean's I/O calls it.
#
# usage: build.sh lean_src uv_src out_dir abi...
set -eu
src=$1/src
uv=$2
out=$3
shift 3
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
sdk=${ANDROID_HOME:-$HOME/android-sdk}
ndk=$(ls -d "$sdk"/ndk/* | sort -V | tail -1)
bin=$ndk/toolchains/llvm/prebuilt/linux-x86_64/bin
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
T=$("$ELAN_HOME/bin/lean" --print-prefix)
api=29
[ -d "$root/out/initc" ] || "$root/tools/gen_init_c.sh" "$root/out/initc"

# headers: the toolchain's, with a config.h of this build
inc=$out/include
mkdir -p "$inc"
cp -r "$T/include/lean" "$inc/"
sed 's/^#define LEAN_MIMALLOC$//' "$T/include/lean/config.h" > "$inc/lean/config.h"
echo '#define LEAN_GITHASH ""' > "$inc/githash.h"

uvsrc="src/fs-poll.c src/idna.c src/inet.c src/random.c src/strscpy.c src/strtok.c src/thread-common.c
  src/threadpool.c src/timer.c src/uv-common.c src/uv-data-getter-setters.c src/version.c
  src/unix/async.c src/unix/core.c src/unix/dl.c src/unix/fs.c src/unix/getaddrinfo.c src/unix/getnameinfo.c
  src/unix/loop-watcher.c src/unix/loop.c src/unix/pipe.c src/unix/poll.c src/unix/process.c
  src/unix/random-devurandom.c src/unix/signal.c src/unix/stream.c src/unix/tcp.c src/unix/thread.c
  src/unix/tty.c src/unix/udp.c src/unix/linux.c src/unix/procfs-exepath.c src/unix/random-getentropy.c
  src/unix/random-getrandom.c src/unix/random-sysctl-linux.c src/unix/proctitle.c"
stubbed="openssl.cpp"
rt="debug.cpp thread.cpp mpz.cpp utf8.cpp object.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
  stackinfo.cpp compact.cpp init_module.cpp io.cpp hash.cpp byteslice.cpp platform.cpp alloc.cpp
  allocprof.cpp sharecommon.cpp stack_overflow.cpp process.cpp object_ref.cpp mpn.cpp mutex.cpp
  libuv.cpp uv/net_addr.cpp uv/event_loop.cpp uv/timer.cpp uv/tcp.cpp uv/udp.cpp uv/dns.cpp uv/system.cpp
  uv/signal.cpp"

# each $1 file (relative to $2) compiled with $3 into $4/<name>.o
each() {
  for f in $1; do echo "$f"; done | xargs -P "$(nproc)" -I{} sh -c \
    "$3 -c '$2/{}' -o '$4/'\$(echo {} | tr / _).o"
}

for abi in "$@"; do
  case $abi in
    arm64-v8a) tgt=aarch64-linux-android$api ;;
    x86_64)    tgt=x86_64-linux-android$api ;;
    *) echo "unknown abi $abi"; exit 2 ;;
  esac
  o=$out/$abi
  mkdir -p "$o/uv" "$o/rt" "$o/init"
  each "$uvsrc" "$uv" "$bin/clang --target=$tgt -O2 -fPIC -w -D_GNU_SOURCE -D_FILE_OFFSET_BITS=64"\
"   -D_LARGEFILE_SOURCE -I$uv/include -I$uv/src" "$o/uv"
  rm -f "$o/libuv.a"
  "$bin/llvm-ar" rcs "$o/libuv.a" "$o"/uv/*.o
  flags="--target=$tgt -O3 -fPIC -ffunction-sections -fdata-sections -w -DNDEBUG -DLEAN_MULTI_THREAD"
  flags="$flags -I$inc -I$src -I$uv/include"
  each "$rt" "$src/runtime" "$bin/clang++ $flags -std=c++20" "$o/rt"
  each "$stubbed" "$src/runtime" "$bin/clang++ $flags -std=c++20 -DLEAN_EMSCRIPTEN" "$o/rt"
  rm -f "$o/libleanrt.a"
  "$bin/llvm-ar" rcs "$o/libleanrt.a" "$o"/rt/*.o
  each "$(cd "$root/out/initc" && find . -name '*.c' | sed 's|^\./||')" "$root/out/initc" \
    "$bin/clang $flags" "$o/init"
  rm -f "$o/libInit.a"
  "$bin/llvm-ar" rcs "$o/libInit.a" "$o"/init/*.o
  echo "built $o: libuv.a libleanrt.a libInit.a"
done
