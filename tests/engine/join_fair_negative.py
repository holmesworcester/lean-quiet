#!/usr/bin/env python3
"""A runtime starvation control, compiled in an isolated source snapshot."""
import pathlib
import subprocess
import sys

scratch, output, original_root = map(pathlib.Path, sys.argv[1:])
output.mkdir(parents=True, exist_ok=True)
source = scratch / "engine/wire/Tcp.lean"
text = source.read_text()
old_pending = """        if st.pending.length < cfg.maxPending then
          st := { st with pending := st.pending ++ [(addr, [b])], waiting := DialQueue.enqueue cfg.maxPending addr st.waiting }"""
drop_when_full = """        if ← st.slots.take cfg addr then
          st := { st with pending := st.pending ++ [(addr, [b])] }
          let _ ← IO.asTask (prio := .dedicated) (dialOut ch st.slots addr)"""
cases = [
    ("strict-priority", "Inbox.next writeFirst writes.tryRecv ch.tryRecv",
     "Inbox.next true writes.tryRecv ch.tryRecv", "--expect-starvation"),
    ("drop-deferred-hint", old_pending, drop_when_full, "--expect-hint-starvation"),
]
for name, old, new, expected in cases:
    assert text.count(old) == 1, f"{name} mutation must match the real runner"
    source.write_text(text.replace(old, new))
    (output / (name + "-Tcp.lean")).write_text(source.read_text())
    with (output / (name + "-build.log")).open("w") as log:
        result = subprocess.run(["lake", "build", "join_fair"], cwd=scratch,
                                stdout=log, stderr=subprocess.STDOUT, timeout=300)
    if result.returncode:
        raise SystemExit(f"{name} mutant must compile; see {output}")
    subprocess.run([sys.executable, str(original_root / "tests/engine/join_fair.py"),
        "--binary", str(scratch / ".lake/build/bin/join_fair"),
        "--out", str(output / name), expected] +
        (["--ordered-hints", "--join-only"] if name == "drop-deferred-hint" else []), check=True)
