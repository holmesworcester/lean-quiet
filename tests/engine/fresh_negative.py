"""Negative controls of the send lanes (docs/SYNC.md, "Lanes"), in an
isolated snapshot: each mutant must fail its law, or the TCP test."""
import pathlib, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)

def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode

assert run(["lake", "build", "engine.wire.LaneLaws", "fresh_tcp"], "baseline-build") == 0
assert run([".lake/build/bin/fresh_tcp"], "baseline-run") == 0
# (name, source, unique original, mutant, target, expected failure text, runtime?)
cases = [
    ("shared-fifo", "engine/wire/Lanes.lean",
     "  match ← writes with\n  | some w => return some (.inl w)\n  | none => return (← events).map .inr",
     "  match ← events with\n  | some e => return some (.inr e)\n  | none => return (← writes).map .inl",
     "engine.wire.LaneLaws", "error:", False),
    ("one-lane", "engine/wire/Lanes.lean",
     "  | .urgent, f => { q with urgent := q.urgent ++ [f] }",
     "  | .urgent, f => { q with serve := q.serve ++ [f] }",
     "engine.wire.LaneLaws", "error:", False),
    ("no-burst-cap", "engine/wire/Lanes.lean",
     "    let (a, b) := fill (burst - f.size) fs\n    (f :: a, b)",
     "    (f :: fs, [])",
     "engine.wire.LaneLaws", "error:", False),
    ("no-credit", "engine/wire/Lanes.lean",
     "def credit (window wantBytes queued : Nat) : Nat := max 1 (min wantBytes (window - queued))",
     "def credit (window wantBytes queued : Nat) : Nat := max 1 wantBytes",
     "engine.wire.LaneLaws", "error:", False),
    ("no-hot", "engine/wire/Node.lean",
     "  else if n.hot.any (fun p => p.1 == o.id && now ≤ p.2 + x.cfg.hotMs) then .urgent else .serve",
     "  else .serve",
     "engine.wire.LaneLaws", "error:", False),
    ("cold-write", "engine/wire/Node.lean",
     "  (n.heat x n.fresh now).finish x out now",
     "  n.finish x out now",
     "engine.wire.WorldLaws", "error:", False),
    ("blocking-send", "engine/wire/Tcp.lean",
     "    unless ps.isEmpty do s.push ps",
     "    for (_, b) in ps do discard <| sendOn s.client b",
     "fresh_tcp", "P gets all 64 ops while S never reads", True),
]
for name, source, old, new, target, expected, runtime in cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, new))
        code = run(["lake", "build", target], name + "-build")
        if runtime:
            assert code == 0, (name, "mutant must compile before runtime control")
            code = run([".lake/build/bin/" + target], name)
            text = (logs / (name + ".log")).read_text()
        else:
            text = (logs / (name + "-build.log")).read_text()
        assert code != 0 and expected in text, (name, "survived or failed for a different reason")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
    assert run(["lake", "build", target], name + "-restored") == 0, (name, "restored source did not build")
assert run(["lake", "build", "engine.wire.LaneLaws", "fresh_tcp"], "restored-build") == 0
assert run([".lake/build/bin/fresh_tcp"], "restored-run") == 0
print(f"fresh negative controls: {len(cases)} refused; restored suite passes")
