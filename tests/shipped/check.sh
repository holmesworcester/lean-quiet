#!/usr/bin/env bash
# Regression controls for the shipped SQLite and the native C twin.
# Each mutation lives in a disposable snapshot. Require a passing
# baseline, a successful mutant build, and the intended runtime failure.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
part=${1:?engine or app}
art=$PWD/out/shipped/$part
mkdir -p "$art"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/shipped-nc.XXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/renderer/Platform.lean \
  platforms/headless/TwinDemo.lean tests/engine/SqliteBuild.lean tests/app/host_twin_demo.sh

mutate() {
  python3 - "$tmp/w/$1" "$2" "$3" <<'PY'
from pathlib import Path
import sys
p, old, new = Path(sys.argv[1]), *sys.argv[2:]
s = p.read_text()
assert s.count(old) == 1, f'mutation must match once: {old!r}'
p.write_text(s.replace(old, new))
PY
}
copy() { rm -rf "$tmp/w"; cp -a "$tmp/base" "$tmp/w"; }
check() {
  if [ "$part" = engine ]; then
    readelf -d "$tmp/w/.lake/build/bin/sqlite_build" > "$art/$1-link.txt"
    if grep -q 'NEEDED.*libsqlite' "$art/$1-link.txt"; then
      echo 'FAIL: dynamic SQLite linkage'; return 1
    fi
    (cd "$tmp/w" && .lake/build/bin/sqlite_build)
  else
    (cd "$tmp/w" && tests/app/host_twin_demo.sh "$art/$1")
  fi
}
build() { (cd "$tmp/w" && lake build "$target") > "$art/$1-build.log" 2>&1; }
killed() {
  build "$1"
  if check "$1" > "$art/$1.log" 2>&1; then
    echo "FAIL: mutant survived: $1"; exit 1
  fi
  grep -q "$2" "$art/$1.log"
  echo "killed by native checks: $1"
}

case $part in
  engine) target=sqlite_build ;;
  app) target=twin_demo ;;
  *) echo "expected engine or app" >&2; exit 2 ;;
esac
copy
build baseline
check baseline > "$art/baseline.log" 2>&1
if [ "$part" = engine ]; then
  mutate third_party/sqlite/quiet_config.h '#define SQLITE_THREADSAFE 2' '#define SQLITE_THREADSAFE 1'
  killed threadsafe 'FAIL: THREADSAFE=2'
  copy
  mutate lakefile.lean '  buildStaticLib (pkg.staticLibDir / nameToStaticLib "sqlite") #[o]' \
    '  let _ := o
  inputBinFile <| FilePath.mk "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0"'
  killed system-sqlite 'FAIL: dynamic SQLite linkage'
else
  mutate platforms/headless/host.c 'hs.ime = show ? 900 : 0;' 'hs.ime = 0;'
  killed keyboard 'FAIL a composer tap opens the keyboard'
  copy
  # the screen dumped somewhere the checks do not read (an absolute path to
  # the same file is no longer a mutant: host.c's !dump takes the whole path)
  mutate tests/app/host_twin_demo.sh '!dump start.ppm' '!dump elsewhere.ppm'
  killed dump-path 'FAIL composer above the navigation bar'
fi
echo "shipped $part negative controls: PASS (scratch mutations discarded)"
