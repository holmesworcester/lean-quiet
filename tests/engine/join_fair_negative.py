#!/usr/bin/env python3
"""A runtime starvation control, compiled in an isolated source snapshot."""
import pathlib
import subprocess
import sys

scratch, output, original_root = map(pathlib.Path, sys.argv[1:])
output.mkdir(parents=True, exist_ok=True)
tcp_source = scratch / "engine/wire/Tcp.lean"
loop_source = scratch / "engine/wire/Loop.lean"
originals = {source: source.read_text() for source in [tcp_source, loop_source]}
old_pending = """        if st.pending.length < cfg.maxPending then
          st := { st with pending := st.pending ++ [(addr, [b])], waiting := DialQueue.enqueue cfg.maxPending addr st.waiting }"""
drop_when_full = """        if ← st.slots.take cfg addr then
          st := { st with pending := st.pending ++ [(addr, [b])] }
          let _ ← IO.asTask (prio := .dedicated) (dialOut ch st.slots addr)"""
cases = [
    ("strict-priority", loop_source, "Inbox.Priority.next state.slot backend.writes backend.events",
     "Inbox.Priority.next Inbox.Priority.first backend.writes backend.events", "--expect-starvation"),
    ("drop-deferred-hint", tcp_source, old_pending, drop_when_full, "--expect-hint-starvation"),
]
for name, source, old, new, expected in cases:
    for path, original in originals.items():
        path.write_text(original)
    text = originals[source]
    assert text.count(old) == 1, f"{name} mutation must match the real runner"
    source.write_text(text.replace(old, new))
    (output / (name + "-" + source.name)).write_text(source.read_text())
    with (output / (name + "-build.log")).open("w") as log:
        result = subprocess.run(["lake", "build", "join_fair"], cwd=scratch,
                                stdout=log, stderr=subprocess.STDOUT, timeout=300)
    if result.returncode:
        raise SystemExit(f"{name} mutant must compile; see {output}")
    subprocess.run([sys.executable, str(original_root / "tests/engine/join_fair.py"),
        "--binary", str(scratch / ".lake/build/bin/join_fair"),
        "--out", str(output / name), expected] +
        (["--ordered-hints", "--join-only"] if name == "drop-deferred-hint" else []), check=True)

# A busy network must not take away local work's preferred slots either.
# Mutate the actual application turn, then require its unchanged phase law
# to reject that runtime implementation. A failed unrelated dependency is
# not accepted as this control's success.
for path, original in originals.items():
    path.write_text(original)
old = "Inbox.Priority.next state.slot backend.writes backend.events"
assert originals[loop_source].count(old) == 1
loop_source.write_text(originals[loop_source].replace(old,
    "Inbox.Priority.next ⟨0, by decide⟩ backend.writes backend.events"))
(output / "network-first-Loop.lean").write_text(loop_source.read_text())
log_path = output / "network-first-law-rejection.log"
with log_path.open("w") as log:
    result = subprocess.run(["lake", "build", "+engine.wire.LoopLaws"], cwd=scratch,
                            stdout=log, stderr=subprocess.STDOUT, timeout=300)
log = log_path.read_text()
if result.returncode == 0 or not all(marker in log for marker in
        ["error: engine/wire/LoopLaws.lean", "type mismatch"]):
    raise SystemExit(f"network-first mutation must be rejected by actual turn laws; see {log_path}")
print("network-first runtime mutation rejected by the unchanged turn laws")
