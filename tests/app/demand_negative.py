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
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
os.environ.setdefault("ELAN_HOME", "/mnt/storage/elan")
os.environ["PATH"] = os.environ["ELAN_HOME"] + "/bin:" + os.environ["PATH"]
os.environ.setdefault("TMPDIR", "/mnt/storage/holmes-tmp")
LOGS = ROOT / "out/component-demand/negative"
LOGS.mkdir(parents=True, exist_ok=True)


def run(args, cwd, name, timeout=300):
    try:
        p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        partial = e.stdout or ""
        if isinstance(partial, bytes):
            partial = partial.decode(errors="replace")
        (LOGS / (name + ".log")).write_text(partial + "\nTIMEOUT\n")
        raise
    (LOGS / (name + ".log")).write_text(p.stdout)
    return p


def no_runtime_crash(p):
    return not any(marker in p.stdout.lower() for marker in
                   ["panic", "uncaught exception", "segmentation fault", "assertion violation"])


cases = [
    ("presentation-completes-on-accept", "component_demand", [
        ("engine/renderer/Session.lean", "published, publication raw serial.toUInt64, completed raw serial.toUInt64",
         "published, publication raw serial.toUInt64, some (publication raw serial.toUInt64, 0)"),
    ], "FAIL: accepted asynchronous staging records one candidate without releasing an obligation"),
    ("presentation-ignores-native-shift", "component_demand", [
        ("app/Screen.lean", "(result.completed.filter fun receipt => receipt.2 == 0).map Prod.fst", "result.completed.map Prod.fst"),
    ], "FAIL: a matching native completion shifted off the recorded viewport does not release"),

    ("presentation-blank-band", "component_demand", [
        ("app/Screen.lean", "findPresentationBand s { r with data := flight.data, lay := flight.lay }",
         "some (flight.lay.textY, max 1 s.dim.lineH)"),
    ], "FAIL: a tall inkless prefix is skipped and actual committed glyph pixels become visible"),
    ("presentation-admits-inkless", "component_demand", [
        ("app/Screen.lean", "if s.chips.isEmpty && !composerHasInk s t then", "if false then"),
    ], "FAIL: a wholly inkless composer draft is refused before outbox or presentation admission"),
    ("presentation-no-root-pin", "net_join", [
        ("app/Screen.lean", "    modify fun s => { s with anchor := some e.root }", "    modify fun s => { s with anchor := none }"),
        ("platforms/headless/NetJoin.lean", "UiFair.run a8 b5 sb\n", "UiFair.run a8 b5 sb (evict := true)\n"),
    ], "FAIL: write 0 painted as committed within 64 app frames"),
    ("presentation-not-visible", "component_demand", [
        ("app/Screen.lean", "if visible && committed && drawn then", "if committed then"),
    ], "FAIL: a real native frame containing blank pixels does not acknowledge the message"),
    ("presentation-rejected", "component_demand", [
        ("app/Screen.lean", "let published := result.accepted", "let published := true"),
    ], "FAIL: a native rejected publication cannot acknowledge otherwise visible body pixels"),
    ("presentation-receipt-needs-new-frame", "component_demand", [
        ("app/Screen.lean", "if s.page == .chat && s.sheet.isNone then\n    if let some e := s.ownSends.head then",
         "if published && s.page == .chat && s.sheet.isNone then\n    if let some e := s.ownSends.head then"),
    ], "FAIL: a refused new publication consumes the exact prior native completion in one presentation step"),
    ("presentation-loses-ancestors", "component_demand", [
        ("app/Screen.lean", "Reader.judgeWrite s.rd s.out w", "Reader.judgeWrite s.rd #[] w"),
    ], "FAIL: eight sequential signed sends enter a bounded FIFO while their first ancestor is uncommitted"),
    ("presentation-replaces-full", "component_demand", [
        ("app/Screen.lean", "if present && s.ownSends.entries.length ≥ Presentation.capacity then return ← presentationRefusal", "if present && s.ownSends.entries.length ≥ Presentation.capacity then modify fun s => { s with ownSends := s.ownSends.pop }"),
        ("app/Screen.lean", "let mut ownSends := s.ownSends", "let mut ownSends := (← get).ownSends"),
        ("app/Screen.lean", "if ownSends.entries.length == s.ownSends.entries.length then return ← presentationRefusal", "if false then return ← presentationRefusal"),
    ], "FAIL: full presentation capacity refuses the ninth send without replacing an obligation or draft"),

    ("frame-pauses-worker", "component_demand", [
        ("app/Screen.lean", "  stepCore evs\n", "  (← get).raster.pause true\n  try stepCore evs finally (← get).raster.pause false\n"),
    ], "FAIL: actual App.step permits retained raster progress during frame assembly"),
    ("replace-first-paint", "component_demand", [
        ("app/community/channel/message/attachment/Screen.lean", "(first || old.version == version)", "old.version == version"),
    ], "FAIL: reaction churn preserves the original admitted ticket and queue position"),
    ("adopt-churning-layout", "component_demand", [
        ("app/Screen.lean", "if d != r.data && !deferRowPaint s x r d then", "if d != r.data then"),
    ], "FAIL: alternating reaction-row geometry cannot replace the committed snapshot"),
    ("optimistic-counts-as-committed", "component_demand", [
        ("app/Screen.lean", "r.shownCommitted || (value.isSome && !flight.data.pending)", "r.shownCommitted || value.isSome"),
    ], "FAIL: real paused writer produces an already shown optimistic bitmap"),
    ("missed-remount", "component_demand", [
        ("app/Screen.lean", "!s.wantSet.contains w || (board.get? w).isNone", "!s.wantSet.contains w"),
    ], "FAIL: unmount and remount between passes refills the revoked board answer"),
    ("obsolete-work", "component_demand", [
        ("engine/renderer/Work.lean", "jobs := s.jobs.filter (fun j => plan.current j.ticket)", "jobs := s.jobs"),
        ("engine/renderer/Work.lean", "let current ← p.state.atomically do return (← get).plan.current job.ticket", "let current := true"),
    ], "FAIL: fast viewport changes discard every obsolete queued action"),
    ("prefetch-first", "component_demand", [
        ("engine/renderer/Work.lean", "Demand.next (fun t => s.plan.visible t.key)", "Demand.next (fun _ => false)"),
    ], "FAIL: visible work runs before earlier prefetch"),
    ("reader-continues", "component_demand", [
        ("app/Screen.lean", "if !(← s.enabled) then return default", "if false then return default"),
    ], "FAIL: superseded reader stops at the next query boundary"),
    ("reader-restores-failed-position", "component_demand", [
        ("app/Screen.lean", '  let rd := (← get).rd\n  rd.exec "BEGIN"',
         '  let rd := (← get).rd\n  let priorQueue ← sh.queue.get\n  rd.exec "BEGIN"'),
        ("app/Screen.lean", '  catch e =>\n    rd.exec "ROLLBACK"\n    throw e',
         '  catch e =>\n    sh.queue.modify (fun _ => priorQueue)\n    rd.exec "ROLLBACK"\n    throw e'),
    ], "FAIL: repeatable read failure cannot starve a retained later query across transaction rollback"),
    ("child-never-unmounts", "op_components", [
        ("app/Screen.lean", "if Raster.near childBottom bx.h offset viewport imageOver then", "if true then"),
    ], "FAIL: offscreen attachment children release every chunk query"),
    ("pending-outside-window", "op_components", [
        ("app/Commands.lean", "let pending := mine.filter (fun p => rows.any (·.1.2 == p.op.id))", "let pending := mine"),
    ], "FAIL: an out-of-window pending row cannot change a bounded answer's pending flags"),

]

if sys.argv[1:]:
    selected = set(sys.argv[1:])
    assert selected <= {case[0] for case in cases}, "unknown mutation"
    cases = [case for case in cases if case[0] in selected]

with tempfile.TemporaryDirectory(prefix="demand-negative-", dir=os.environ["TMPDIR"]) as tmp:
    base, work = Path(tmp) / "base", Path(tmp) / "work"
    snapshot = run(["bash", "-c", '. tests/snapshot.sh\nsnapshot "$1" engine/core engine/wire engine/sync engine/renderer app platforms/headless tests/app tests/engine Quiet.lean assets', "snapshot", str(base)], ROOT, "snapshot")
    assert snapshot.returncode == 0, "snapshot failed"
    assert run(["lake", "build", "component_demand", "op_components", "net_join"], base, "baseline-build").returncode == 0, "baseline build failed"
    for exe in ["component_demand", "op_components", "net_join"]:
        p = run([str(base / ".lake/build/bin" / exe), str(LOGS / "baseline")], base, "baseline-" + exe)
        assert p.returncode == 0 and no_runtime_crash(p), "baseline failed"
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
            assert p.returncode == 1 and expected in p.stdout and no_runtime_crash(p), (name, "wrong failure", p.stdout[-2000:])
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
