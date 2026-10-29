#!/usr/bin/env python3
"""Kill the child we started, then restore exactly the same SQLite files."""
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import time
sys.dont_write_bytecode = True
from lifecycle_env import network_env

root = Path(__file__).resolve().parents[2]
out = (root / (sys.argv[1] if len(sys.argv) > 1 else "out/app-lifecycle")).resolve()
out.mkdir(parents=True, exist_ok=True)
exe = root / ".lake/build/bin/app_lifecycle"
env = network_env()
subprocess.run([str(exe), str(out)], cwd=root, env=env, check=True)
log = (out / "crash.stderr").open("w")
p = subprocess.Popen([str(exe), str(out), "crash"], cwd=root,
                     stdout=subprocess.PIPE, stderr=log, text=True, env=env)
(out / "crash.pid").write_text(str(p.pid) + "\n")
try:
    deadline = time.monotonic() + 45
    ready = False
    while p.poll() is None and time.monotonic() < deadline:
        if select.select([p.stdout], [], [], 0.2)[0]:
            if p.stdout.readline().strip() == "READY":
                ready = True
                break
    assert ready, "child did not commit its checkpoint"
    os.kill(p.pid, signal.SIGKILL)
    assert p.wait(timeout=10) == -signal.SIGKILL
finally:
    if p.poll() is None:
        os.kill(p.pid, signal.SIGKILL)
        p.wait(timeout=10)
    log.close()
# Verify twice: replay is idempotent on the next cold start, too.
for _ in range(2):
    subprocess.run([str(exe), str(out), "verify"], cwd=root, env=env, check=True, timeout=30)
print("lifecycle subprocess: 1 SIGKILL, 2 cold restores passed")
