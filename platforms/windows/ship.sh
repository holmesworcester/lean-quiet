#!/usr/bin/env bash
# All large artifacts stay under the worktree's out/ and the storage-backed VM.
set -euo pipefail
cd "$(dirname "$0")/../.."
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
vm=${WINDOWS_VM:-/mnt/storage/windows-quiet-vm}
mode=${1:-build}
mkdir -p out/windows
exec 9>"${WINDOWS_LOCK:-/mnt/storage/holmes-wt/winvm.lock}"
flock -w 60 9 || { echo 'Windows VM is in use' >&2; exit 1; }
platforms/windows/toolchain.sh
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
python3 platforms/windows/stage.py >out/windows/stage.log 2>&1 || { tail -n 40 out/windows/stage.log; exit 1; }
rustup target add x86_64-pc-windows-gnu
CARGO_TARGET_DIR="$PWD/out/rust" cargo build --manifest-path engine/native/crypto/Cargo.toml --locked --release --target x86_64-pc-windows-gnu
cp /usr/x86_64-w64-mingw32/lib/libntdll.a out/windows/stage/glue/
cp out/rust/x86_64-pc-windows-gnu/release/liblq_crypto.a out/windows/stage/glue/
if [ "$mode" = e2e ]; then
  WINDOWS_MAIN=tests.engine.JoinTcp WINDOWS_SOURCES=sources-jointcp.txt python3 platforms/windows/stage.py >out/windows/stage-net.log 2>&1 || { tail -n 40 out/windows/stage-net.log; exit 1; }
  WINDOWS_MAIN=tests.engine.Restart WINDOWS_SOURCES=sources-restart.txt python3 platforms/windows/stage.py >out/windows/stage-restart.log 2>&1 || { tail -n 40 out/windows/stage-restart.log; exit 1; }
fi
if [ "$mode" = stage ]; then exit; fi
platforms/windows/native.sh
share=$vm/shared/lean-quiet-windows
mkdir -p "$share/toolchain" "$share/results"
rsync -a --include='/bin/***' --include='/include/***' --include='/lib/' --include='/lib/lean/' --include='/lib/lean/*.a' --include='/lib/clang/***' --include='/lib/*.a' --include='/lib/*.o' --exclude='*' out/toolchain/lean-4.35.0-windows/ "$share/toolchain/"
rsync -a out/windows/stage/ "$share/stage/"
python3 "$vm/vm.py" start
python3 "$vm/vm.py" exec platforms/windows/build.ps1 --timeout 1800 >out/windows/build.log 2>&1 || { cat out/windows/build.log; exit 1; }
cp "$share/results/LeanQuiet-windows-x64.zip" out/windows/
if [ "$mode" = e2e ]; then
  python3 "$vm/vm.py" exec platforms/windows/network.ps1 --timeout 1800 >out/windows/network.log 2>&1 || { cat out/windows/network.log; rsync -a "$share/results/" out/windows/; exit 1; }
  python3 "$vm/vm.py" exec platforms/windows/test.ps1 --timeout 600 >out/windows/e2e.log 2>&1 || { cat out/windows/e2e.log; rsync -a "$share/results/" out/windows/; exit 1; }
  rsync -a "$share/results/" out/windows/
  cat out/windows/e2e.log out/windows/network.log
elif [ "$mode" = run ]; then
  python3 "$vm/vm.py" exec platforms/windows/run.ps1 --timeout 60
fi
cat out/windows/build.log
