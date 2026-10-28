#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root=$PWD
out=$root/out/appearance/seam
mkdir -p "$out"
ln -sfn "$root/assets" "$out/assets"
cat > "$out/script" <<'SCRIPT'
theme system
!theme dark
!frames 3
theme
!dump dark.ppm
!theme light
!frames 3
theme
!dump light.ppm
theme dark
!theme light
!frames 3
theme
!dump forced.ppm
SCRIPT
(cd "$out" && QUIET_SCRIPT="$out/script" "$root/.lake/build/bin/appearance_seam") > "$out/replies" 2>&1
python3 - "$out" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]); replies=(p/'replies').read_text()
assert 'theme system effective Theme.Value.dark' in replies
assert 'theme system effective Theme.Value.light' in replies
assert 'theme dark effective Theme.Value.dark' in replies
for name,want in [('light',bytes.fromhex('f7f7f7')),('dark',bytes.fromhex('242424')),('forced',bytes.fromhex('242424'))]:
    data=(p/(name+'.ppm')).read_bytes().split(b'\n',3)[3]
    assert data[:3] == want, (name,data[:3])
print('native headless seam: 3 OS/setting replies and 3 frame pixel checks pass')
PY
