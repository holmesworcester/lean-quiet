"""Each mutant is built alone in a disposable snapshot, then restored."""
import pathlib
import subprocess
import sys

root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)


def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=300).returncode


assert run(["lake", "build", "fullsync", "engine.sync.StateLaws"], "baseline-build") == 0
assert run([".lake/build/bin/fullsync", "512"], "baseline-run") == 0
# name, source, old, mutant, target, runtime assertion (None means proof)
cases = [
    ("full-bookkeeping", "engine/sync/Conn.lean",
     "    known := sent.foldl (fun (k : HashSet Id) (o : Op) => remember cfg.maxKnown k o.id) c.known }",
     "    known := sent.foldl (fun (k : HashSet Id) (o : Op) => remember cfg.maxKnown k o.id) c.known\n"
     "    offered := sent.foldl (fun (k : HashSet Id) (o : Op) => k.insert o.id) c.offered }",
     "fullsync", "full round keeps no sender per-op state"),
    ("stream-unbounded", "engine/sync/Conn.lean",
     "offered := remember cfg.maxKnown c.offered i", "offered := c.offered.insert i",
     "fullsync", "stream hint is bounded"),
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
            expected = "error: engine/sync/"
        assert code != 0 and expected in text, (name, "survived or failed elsewhere")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0
assert run(["lake", "build", "fullsync", "engine.sync.StateLaws"], "restored-build") == 0
assert run([".lake/build/bin/fullsync", "512"], "restored-run") == 0
print(f"stateless negative controls: {len(cases)} refused; restored suite passes")
