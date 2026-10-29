#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
test -f assets/font.bin
python3 platforms/linux/font.py assets/font.bin out/desktop/font.bin
lake build desktop engine.renderer.desktop.Laws platforms.desktop.Laws
# the desktop's laws, on standard axioms only (tests/app/DesktopAxioms.lean)
out=$(lake env lean tests/app/DesktopAxioms.lean 2>&1)
want=$(grep -c "^#print axioms" tests/app/DesktopAxioms.lean)
n=$(grep -c "depends on axioms\|does not depend on any axioms" <<<"$out" || true)
[ "$n" -eq "$want" ] || { echo "$out"; echo "expected $want desktop axiom reports, got $n" >&2; exit 1; }
bad=$(grep "depends on axioms" <<<"$out" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
[ -z "$bad" ] || { echo "non-standard axioms: $bad" >&2; exit 1; }
echo "desktop: all $want laws rest on standard axioms only"
.lake/build/bin/desktop out/desktop
# Full pixel comparison against pinned libquiet renders is visual:compare,
# invoked by local CI. No hand-maintained CSS screenshot stand-in here.
