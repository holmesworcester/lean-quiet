#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p out/fling
cc -std=c11 -Wall -Wextra -Werror -g -fsanitize=address,undefined platforms/native/fling_test.c -lm -o out/fling/test
ASAN_OPTIONS=detect_leaks=0 out/fling/test
# A negative control restores the release-velocity bug in the actual core.
python3 - <<'PY'
from pathlib import Path
p = Path('platforms/native/fling.h').read_text()
assert 'out.delta != 0 && now > s->time' in p
Path('out/fling/fling.h').write_text(p.replace('out.delta != 0 && now > s->time', 'now > s->time'))
Path('out/fling/fling_test.c').write_text(Path('platforms/native/fling_test.c').read_text())
PY
cc -std=c11 out/fling/fling_test.c -lm -o out/fling/broken
ulimit -c 0
if out/fling/broken > out/fling/negative.log 2>&1; then
  echo 'ERROR: regression test accepted lost release velocity' >&2
  exit 1
fi
echo 'fling: zero-velocity release regression rejected'
