#!/usr/bin/env python3
"""Mutation controls of the running workers and component integration.

Build a scratch copy first; each runtime mutant must compile and fail its
specific assertion. Keep logs on failure, never mutate the working tree.
"""
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
os.environ.setdefault("ELAN_HOME", "/mnt/storage/elan")
os.environ["PATH"] = os.environ["ELAN_HOME"] + "/bin:" + os.environ["PATH"]
os.environ.setdefault("TMPDIR", "/mnt/storage/holmes-tmp")
LOGS = ROOT / "out/component-demand/negative"
LOGS.mkdir(parents=True, exist_ok=True)


def run(args, cwd, name, timeout=300):
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True, timeout=timeout)
    (LOGS / (name + ".log")).write_text(p.stdout)
    return p


cases = [
    ("missed-remount", "component_demand", [
        ("ops/app/Reader.lean", "!s.wantSet.contains w || (board.get? w).isNone", "!s.wantSet.contains w"),
    ], "FAIL: unmount and remount between passes refills the revoked board answer"),
    ("obsolete-work", "component_demand", [
        ("engine/renderer/Work.lean", "jobs := s.jobs.filter (fun j => plan.current j.ticket)", "jobs := s.jobs"),
        ("engine/renderer/Work.lean", "let current ← p.state.atomically do return (← get).plan.current job.ticket", "let current := true"),
    ], "FAIL: fast viewport changes discard every obsolete queued action"),
    ("prefetch-first", "component_demand", [
        ("engine/renderer/Work.lean", "Demand.next (fun t => s.plan.visible t.key)", "Demand.next (fun _ => false)"),
    ], "FAIL: visible work runs before earlier prefetch"),
    ("reader-continues", "component_demand", [
        ("ops/app/Reader.lean", "if !(← s.enabled) then return default", "if false then return default"),
    ], "FAIL: superseded reader stops at the next query boundary"),
    ("child-never-unmounts", "op_components", [
        ("App.lean", "if Raster.near childBottom bx.h offset viewport over then", "if true then"),
    ], "FAIL: offscreen attachment children release every chunk query"),

]

with tempfile.TemporaryDirectory(prefix="demand-negative-", dir=os.environ["TMPDIR"]) as tmp:
    base, work = Path(tmp) / "base", Path(tmp) / "work"
    snapshot = run(["bash", "-c", '. tests/snapshot.sh\nsnapshot "$1" engine/core engine/wire engine/renderer ops platforms/headless tests/app tests/engine App.lean AppTypes.lean AppLife.lean Quiet.lean assets', "snapshot", str(base)], ROOT, "snapshot")
    assert snapshot.returncode == 0, "snapshot failed"
    assert run(["lake", "build", "component_demand", "op_components"], base, "baseline-build").returncode == 0, "baseline build failed"
    for exe in ["component_demand", "op_components"]:
        assert run([str(base / ".lake/build/bin" / exe), str(LOGS / "baseline")], base, "baseline-" + exe).returncode == 0, "baseline failed"
    for name, exe, changes, expected in cases:
        shutil.copytree(base, work, symlinks=True)
        try:
            for file, old, new in changes:
                path = work / file
                source = path.read_text()
                assert source.count(old) == 1, (name, "missing mutation anchor")
                path.write_text(source.replace(old, new))
            assert run(["lake", "build", exe], work, name + "-build").returncode == 0, (name, "must compile before runtime rejection")
            p = run([str(work / ".lake/build/bin" / exe), str(LOGS / name)], work, name)
            assert p.returncode == 1 and expected in p.stdout, (name, "wrong failure", p.stdout[-2000:])
            print("rejected", name, flush=True)
        finally:
            shutil.rmtree(work)
    source = base / "engine/renderer/Demand.lean"
    original = source.read_text()
    for name, old, new, theorem in [
        ("stale-publication", "if p.current t then some value else none", "some value", "complete_retired"),
        ("reused-ticket", "tickets := keys.zipIdx.map fun (k, i) => (p.ticket k).getD ⟨k, p.next + i⟩", "tickets := keys.zipIdx.map fun (k, i) => (p.ticket k).getD ⟨k, 0⟩", "reconcile_ticket_origin"),
    ]:
        assert original.count(old) == 1, (name, "proof mutation anchor")
        source.write_text(original.replace(old, new))
        p = run(["lake", "env", "lean", str(source)], base, name + "-proof")
        # Require an error inside the intended theorem's proof. A parse,
        # import or declaration error elsewhere is not a proof rejection.
        begin = original.index("theorem " + theorem)
        end = original.index("\ntheorem ", begin)
        first = original[:begin].count("\n") + 1
        last = original[:end].count("\n") + 1
        errors = [int(n) for n in re.findall(r"Demand\.lean:(\d+):\d+: error:", p.stdout)]
        assert p.returncode != 0 and any(first <= n < last for n in errors), (name, "proof mutant survived or wrong failure")
        print("rejected", name, "by the proof of running code", flush=True)
