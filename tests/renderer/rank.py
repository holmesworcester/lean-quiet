#!/usr/bin/env python3
"""Actual worker selection checks, infinite kernel witness, strict controls.

Only the small production Demand/Work closure is copied. No source in the
checkout is mutated. Retain every build/run log; timeout is a test failure.
"""
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LOGS = ROOT / "out/demand-rank"
LOGS.mkdir(parents=True, exist_ok=True)
os.environ.setdefault("ELAN_HOME", "/mnt/storage/elan")
os.environ.setdefault("TMPDIR", "/mnt/storage/holmes-tmp")
os.environ["PATH"] = os.environ["ELAN_HOME"] + "/bin:" + os.environ["PATH"]


def run(args, cwd, name, timeout=120):
    try:
        p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        output = e.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        (LOGS / (name + ".log")).write_text(output + "\nTIMEOUT\n")
        raise
    (LOGS / (name + ".log")).write_text(p.stdout)
    return p


def lake(cwd, name, *args):
    return run(["systemd-run", "--user", "--scope", "-p", "MemoryMax=48G", "-p",
                "MemorySwapMax=0", "lake", *args], cwd, name)


def healthy(p):
    return not any(x in p.stdout.lower() for x in
                   ["panic", "uncaught exception", "segmentation fault", "timeout:", "assertion violation"])


cases = [
    ("background-first", "engine/renderer/Work.lean",
     "(fun t => s.plan.visible t.key) true s.jobs", "(fun _ => false) true s.jobs",
     "FAIL: visible request precedes an older background request"),
    ("newest-visible", "engine/renderer/Demand.lean",
     "let found := next (fun v => visible (key v)) background queued",
     "let found := next (fun v => visible (key v)) background queued.reverse",
     "FAIL: retained target satisfies initial all-predecessor bound"),
    ("prepend-admission", "engine/renderer/Work.lean",
     "plan, jobs := s.jobs ++ [job]", "plan, jobs := job :: s.jobs",
     "FAIL: retained target satisfies initial all-predecessor bound"),
    ("count-pending", "engine/renderer/Work.lean",
     "set { s with jobs }", "set { s with jobs, stats := { s.stats with completedSelections := s.stats.completedSelections + 1 } }",
     "FAIL: pending action is not a completed selection"),
]
with tempfile.TemporaryDirectory(prefix="demand-rank-", dir=os.environ["TMPDIR"]) as tmp:
    work = Path(tmp)
    for name in ["lean-toolchain", "engine/renderer/Demand.lean", "engine/renderer/DemandRank.lean",
                 "engine/renderer/Work.lean", "tests/vacuity/DemandRank.lean", "tests/renderer/WorkRank.lean"]:
        dest = work / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, dest)
    (work / "lakefile.lean").write_text('''import Lake
open Lake DSL
package demand_rank
lean_lib Renderer where
  globs := #[.submodules `engine.renderer]
lean_exe work_rank where
  root := `tests.renderer.WorkRank
''')
    p = lake(work, "baseline-build", "build", "work_rank", "engine.renderer.DemandRank")
    assert p.returncode == 0, "baseline compilation failed"
    p = lake(work, "witness", "env", "lean", "tests/vacuity/DemandRank.lean")
    assert p.returncode == 0, "nonempty continuing-run witness failed"
    dependencies = re.findall(r"depends on axioms: \[([^]]*)\]", p.stdout)
    assert len(dependencies) >= 14, "missing law/witness dependency output"
    for deps in dependencies:
        assert set(deps.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, ("unapproved witness dependency", deps)
    for name in ["baseline"]:
        p = run([str(work / ".lake/build/bin/work_rank")], work, name)
        assert p.returncode == 0 and "work_rank: 13 passed, 0 failed" in p.stdout and healthy(p), "baseline runtime failed"
    for name, file, old, new, expected in cases:
        path = work / file
        original = path.read_text()
        assert original.count(old) == 1, (name, "missing unique mutation anchor")
        path.write_text(original.replace(old, new))
        try:
            assert lake(work, name + "-build", "build", "work_rank").returncode == 0, (name, "mutation must compile")
            p = run([str(work / ".lake/build/bin/work_rank")], work, name)
            assert p.returncode == 1 and expected in p.stdout and healthy(p), (name, "wrong failure", p.stdout)
            print("rejected", name, flush=True)
            if name == "newest-visible":
                p = lake(work, name + "-proof", "env", "lean", "engine/renderer/DemandRank.lean")
                src = (work / "engine/renderer/DemandRank.lean").read_text()
                start = src[:src.index("theorem take_progress")].count("\n") + 1
                end = src[:src.index("theorem take_changes")].count("\n") + 1
                errors = [int(n) for n in re.findall(r"DemandRank\.lean:(\d+):\d+: error:", p.stdout)]
                assert p.returncode != 0 and any(start <= line < end for line in errors), "wrong kernel rejection"
                print("rejected newest-visible by the proof of running selection", flush=True)
        finally:
            path.write_text(original)
    assert lake(work, "restored-build", "build", "work_rank", "engine.renderer.DemandRank").returncode == 0
    p = run([str(work / ".lake/build/bin/work_rank")], work, "restored")
    assert p.returncode == 0 and "work_rank: 13 passed, 0 failed" in p.stdout and healthy(p), "restored runtime failed"
    assert lake(work, "restored-witness", "env", "lean", "tests/vacuity/DemandRank.lean").returncode == 0
print("demand rank: 13 real-worker checks, infinite witness, 4 compiling runtime controls and 1 kernel control passed", flush=True)
