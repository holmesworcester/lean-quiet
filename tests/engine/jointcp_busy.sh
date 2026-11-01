#!/usr/bin/env bash
# jointcp under parallel CI: another process already listens on the port
# jointcp would take (its base), and on the next one. jointcp must move
# its sides to free ports and pass all its checks, not fail to bind.
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build jointcp >/dev/null
out=out/jointcp-busy
mkdir -p "$out"
python3 - "$out" <<'PY'
import socket, subprocess, sys
out = sys.argv[1]
held = []
s = socket.socket(); s.bind(('127.0.0.1', 0)); s.listen(); held.append(s)
base = s.getsockname()[1]
t = socket.socket()
try:
    t.bind(('127.0.0.1', base + 1)); t.listen(); held.append(t)
except OSError:
    pass
r = subprocess.run(['.lake/build/bin/jointcp', out, str(base)], capture_output=True, text=True, timeout=600)
open(f'{out}/jointcp.log', 'w').write(r.stdout + r.stderr)
assert all(x.getsockname()[1] in (base, base + 1) for x in held)
if r.returncode != 0:
    sys.exit(f'jointcp failed with its base port {base} held:\n{r.stdout[-2000:]}{r.stderr[-2000:]}')
print(f'jointcp-busy: ports {base} and {base + 1} held by another process; jointcp moved and passed')
PY
