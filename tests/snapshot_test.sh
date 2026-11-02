#!/usr/bin/env bash
# tests/snapshot.sh's own checks, on a small fake tree (nothing built):
# 1. a snapshot listing app carries every engine part, engine/world among
#    them, sources and built tree, though the caller did not list it (the
#    batch-C regression: app/Proofs.lean imports engine.world.Pieces);
# 2. a part listed with a part of it merges, never nesting;
# 3. the negative control: an app import that the snapshot lacks fails
#    `snapshot`, naming the module.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/snapshot-test.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
fail() { echo "FAIL: $*" >&2; exit 1; }

src=$tmp/src
mkdir -p "$src" && cd "$src"
touch lakefile.lean lake-manifest.json lean-toolchain
mkdir -p engine/core engine/world engine/renderer/qr engine/native/crypto/target/release app \
  tests/engine platforms/headless platforms/native third_party/sqlite .lake/build/lib/lean/engine/world
touch engine/native/glue.c engine/native/crypto.c engine/native/listener.h tests/engine/listener_fixture.c \
  platforms/headless/host.c engine/native/crypto/target/release/liblq_crypto.a \
  engine/core/Core.lean engine/renderer/qr/Qr.lean .lake/build/lib/lean/engine/world/Pieces.olean
echo 'import engine.world.Pieces' > app/Proofs.lean
echo 'import engine.core.Core' > engine/world/Pieces.lean
. "$here/tests/snapshot.sh"

snapshot "$tmp/one" engine/core app
[ -f "$tmp/one/engine/world/Pieces.lean" ] || fail "app's snapshot lacks engine/world's source"
[ -f "$tmp/one/.lake/build/lib/lean/engine/world/Pieces.olean" ] || fail "app's snapshot lacks engine/world's build"
[ -f "$tmp/one/engine/renderer/qr/Qr.lean" ] || fail "app's snapshot lacks engine/renderer"

snapshot "$tmp/two" engine/renderer/qr app engine/renderer
[ -f "$tmp/two/engine/renderer/qr/Qr.lean" ] || fail "merge lost engine/renderer/qr"
[ ! -e "$tmp/two/engine/renderer/qr/qr" ] && [ ! -e "$tmp/two/engine/renderer/renderer" ] ||
  fail "a part listed with a part of it nested"

echo 'import tests.engine.Fixture' >> app/Proofs.lean
touch tests/engine/Fixture.lean
if snapshot "$tmp/three" app 2> "$tmp/err"; then
  fail "a snapshot lacking an app import (tests.engine.Fixture) was not refused"
fi
grep -q 'tests.engine.Fixture' "$tmp/err" || fail "the refusal does not name tests.engine.Fixture: $(cat "$tmp/err")"
echo "snapshot: 3 checks passed (app carries the engine, overlaps merge, a missing import is refused)"
