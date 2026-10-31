#!/usr/bin/env python3
"""A runtime starvation control, compiled in an isolated source snapshot."""
import pathlib
import subprocess
import sys

scratch, output, original_root = map(pathlib.Path, sys.argv[1:])
output.mkdir(parents=True, exist_ok=True)
source = scratch / "engine/wire/Tcp.lean"
text = source.read_text()
old = "Inbox.next writeFirst writes.tryRecv ch.tryRecv"
assert text.count(old) == 1, "strict-priority mutation must match the real runner"
source.write_text(text.replace(old, "Inbox.next true writes.tryRecv ch.tryRecv"))
(output / "strict-priority-Tcp.lean").write_text(source.read_text())
with (output / "strict-priority-build.log").open("w") as log:
    result = subprocess.run(["lake", "build", "join_fair"], cwd=scratch,
                            stdout=log, stderr=subprocess.STDOUT, timeout=300)
if result.returncode:
    raise SystemExit(f"strict-priority mutant must compile; see {output}")
subprocess.run([sys.executable, str(original_root / "tests/engine/join_fair.py"),
    "--binary", str(scratch / ".lake/build/bin/join_fair"),
    "--out", str(output / "strict-priority"), "--expect-starvation"], check=True)
