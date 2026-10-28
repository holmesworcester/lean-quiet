#!/bin/sh
# Lean's runtime and Init for iOS: libleanrt.a, libInit.a and libuv.a, as
# platforms/android/leanrt/build.sh builds them for Android (no mimalloc, no GMP,
# OpenSSL in its stub form, libuv from its Darwin source list), with
# Xcode's clang for an SDK. Runs on the Mac, from the tree ship.sh stages.
# (lean-chat's ios/leanrt.sh at b38a42d, unchanged.)
#
# usage: leanrt.sh stage_dir out_dir sdk     (sdk: iphoneos | iphonesimulator)
set -eu
st=$(cd "$1" && pwd); mkdir -p "$2"; out=$(cd "$2" && pwd); sdk=$3
src=$st/lean/src; inc=$st/lean/include; uv=$st/uv
case $sdk in
  iphoneos)        tgt=arm64-apple-ios17.0 ;;
  iphonesimulator) tgt=arm64-apple-ios17.0-simulator ;;
  *) echo "unknown sdk $sdk"; exit 2 ;;
esac
cc="xcrun -sdk $sdk clang --target=$tgt"
cxx="xcrun -sdk $sdk clang++ --target=$tgt"
ar="xcrun -sdk $sdk ar"

uvsrc="src/fs-poll.c src/idna.c src/inet.c src/random.c src/strscpy.c src/strtok.c src/thread-common.c
  src/threadpool.c src/timer.c src/uv-common.c src/uv-data-getter-setters.c src/version.c
  src/unix/async.c src/unix/core.c src/unix/dl.c src/unix/fs.c src/unix/getaddrinfo.c src/unix/getnameinfo.c
  src/unix/loop-watcher.c src/unix/loop.c src/unix/pipe.c src/unix/poll.c src/unix/process.c
  src/unix/random-devurandom.c src/unix/signal.c src/unix/stream.c src/unix/tcp.c src/unix/thread.c
  src/unix/tty.c src/unix/udp.c src/unix/proctitle.c src/unix/bsd-ifaddrs.c src/unix/kqueue.c
  src/unix/random-getentropy.c src/unix/darwin-proctitle.c src/unix/darwin.c src/unix/fsevents.c"
stubbed="openssl.cpp"
rt=$(cat "$st/lean/runtime.txt")

# each $1 file (relative to $2) compiled with $3 into $4/<name>.o
each() {
  # (macOS xargs caps -I's command at 255 bytes: the file goes as $0)
  for f in $1; do echo "$f"; done | xargs -P "$(sysctl -n hw.ncpu)" -n 1 sh -c \
    "$3 -c '$2/'\$0 -o '$4/'\$(echo \$0 | tr / _).o || exit 255"
}

o=$out/$sdk
mkdir -p "$o/uv" "$o/rt" "$o/init"
each "$uvsrc" "$uv" "$cc -O2 -w -D_DARWIN_UNLIMITED_SELECT=1 -D_DARWIN_USE_64_BIT_INODE=1 \
-D_FILE_OFFSET_BITS=64 -D_LARGEFILE_SOURCE -I$uv/include -I$uv/src" "$o/uv"
rm -f "$o/libuv.a"; $ar rcs "$o/libuv.a" "$o"/uv/*.o
flags="-O3 -w -DNDEBUG -DLEAN_MULTI_THREAD -I$inc -I$src -I$uv/include"
# iOS has no system(): the runtime's one call (debug.cpp, to attach a
# debugger) gets one that fails, in a copy of the file.
p=$o/patched/runtime
mkdir -p "$p"
{ echo 'static int lean_ios_no_system(const char*) { return -1; }'
  sed 's/\([^a-z_]\)system(/\1lean_ios_no_system(/' "$src/runtime/debug.cpp"; } > "$p/debug.cpp"
each "$(echo $rt | sed 's/debug.cpp//')" "$src/runtime" "$cxx $flags -std=c++20" "$o/rt"
each debug.cpp "$p" "$cxx $flags -std=c++20" "$o/rt"
each "$stubbed" "$src/runtime" "$cxx $flags -std=c++20 -DLEAN_EMSCRIPTEN" "$o/rt"
rm -f "$o/libleanrt.a"; $ar rcs "$o/libleanrt.a" "$o"/rt/*.o
each "$(cd "$st/initc" && find . -name '*.c' | sed 's|^\./||')" "$st/initc" "$cc $flags" "$o/init"
rm -f "$o/libInit.a"; $ar rcs "$o/libInit.a" "$o"/init/*.o
echo "built $o: libuv.a libleanrt.a libInit.a"
