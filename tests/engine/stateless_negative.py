"""Each mutant is built alone in a disposable snapshot, then restored."""
import pathlib
import subprocess
import sys

root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)


def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=300).returncode


assert run(["lake", "build", "fullsync", "ops.sync.StateLaws", "ops.sync.ClosureComplete"], "baseline-build") == 0
assert run([".lake/build/bin/fullsync", "512"], "baseline-run") == 0
# name, source, old, mutant, target, runtime assertion (None means proof)
cases = [
    ("full-bookkeeping", "ops/sync/Conn.lean",
     " } |>.queue cfg (sent.flatMap Op.reqs)",
     " } |> fun c => { c with offered := sent.foldl (fun k o => k.insert o.id) c.offered, frontier := c.frontier ++ sent.flatMap Op.reqs }",
     "fullsync", "full round keeps no sender per-op state"),
    ("full-law", "ops/sync/Conn.lean",
     "if c.roundFloor ≤ 1 then (c.frontier, false)", "if False then (c.frontier, false)",
     "ops.sync.ClosureLaws", None),
    ("closure-cap", "ops/sync/Closure.lean",
     "frontier ++ fresh.take room", "frontier ++ fresh",
     "ops.sync.StateLaws", None),
    ("closure-cap-runtime", "ops/sync/Closure.lean",
     "frontier ++ fresh.take room", "frontier ++ fresh",
     "fullsync", "a cut never admits more ids that round"),
    ("closure-missing-edge", "ops/sync/Conn.lean",
     "(c.queue cfg o.reqs).walkN", "(c.queue cfg []).walkN",
     "ops.sync.ClosureComplete", None),
    ("stream-unbounded", "ops/sync/Conn.lean",
     "offered := remember cfg.maxKnown c.offered i", "offered := c.offered.insert i",
     "fullsync", "stream hint is bounded"),
    ("hidden-cut", "ops/sync/Closure.lean",
     "Decidable.decide (room < fresh.length)", "false",
     "fullsync", "zero closure cap cuts explicitly"),
    ("live-floor", "ops/sync/Conn.lean",
     "if c.roundFloor ≤ 1 then (c.frontier, false)", "if max c.floor (c.peerFloor.getD c.floor) ≤ 1 then (c.frontier, false)",
     "fullsync", "full captured range survives a later hello"),
]
for name, source, old, mutant, target, expected in cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, mutant))
        code = run(["lake", "build", target], name + "-build")
        if expected:
            assert code == 0, (name, "runtime mutant must compile")
            code = run([".lake/build/bin/fullsync", "512"], name)
            text = (logs / (name + ".log")).read_text()
        else:
            text = (logs / (name + "-build.log")).read_text()
            expected = "error: ops/sync/Closure"
        assert code != 0 and expected in text, (name, "survived or failed elsewhere")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0
assert run(["lake", "build", "fullsync", "ops.sync.StateLaws", "ops.sync.ClosureComplete"], "restored-build") == 0
assert run([".lake/build/bin/fullsync", "512"], "restored-run") == 0
print(f"stateless negative controls: {len(cases)} refused; restored suite passes")
