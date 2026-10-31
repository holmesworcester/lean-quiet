#!/usr/bin/env bash
# COFF native glue, against the host's Windows SDK and matching Clang headers.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
st=$PWD/out/windows/stage
tc=$PWD/out/toolchain/lean-4.34.0-windows
mkdir -p "$st/native"
cc=${WINDOWS_CLANG:-clang}
flags=(--target=x86_64-w64-windows-gnu -O2 -w -I "$tc/include" -isystem /usr/x86_64-w64-mingw32/include -I third_party/sqlite -D_WIN32_WINNT=0x0A00)
"$cc" "${flags[@]}" -c engine/native/glue.c -o "$st/native/glue.o"
"$cc" "${flags[@]}" -c engine/native/crypto.c -o "$st/native/crypto.o"
"$cc" "${flags[@]}" -include third_party/sqlite/quiet_config.h -c third_party/sqlite/sqlite3.c -o "$st/native/sqlite.o"
"$cc" "${flags[@]}" -c platforms/windows/shell.c -o "$st/native/shell.o"
"$cc" "${flags[@]}" -c tests/engine/listener_fixture.c -o "$st/native/listener_fixture.o"
