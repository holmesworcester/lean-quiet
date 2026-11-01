#!/usr/bin/env python3
"""Production TCP/SQLite ingress and cancellation, with compiling controls.

The optional comma-separated case filter supports parallel local diagnosis;
CI and the named task omit it and run all eight cases. Mutants use a private
snapshot and never alter the sources or build artifacts under test.
"""
from pathlib import Path
import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/vacuity"))
from runtime import run_checked

CASES = [
    ("cursor-reset", "engine/wire/Ingress.lean", "--fair-only",
     "  (found, { slots, cursor })", "  (found, { slots, cursor := ⟨0, by omega⟩ })", 1,
     "honest peer frame is applied within four times the fixed source count"),
    ("reuse-live-source", "engine/wire/IngressIO.lean", "--quota-only",
     "        unless r.live[i] do", "        if i == 1 then", 1,
     "quota reuse before a due-tick reap cannot grow the retained socket table"),
    ("uncancelled-peer-send", "engine/wire/IngressIO.lean", "--cancel-only",
     "    | .closed => return false", "    | .closed => IO.sleep 1", 1,
     "retirement cancels a real TCP reader blocked on its peer mailbox"),
    ("overwrite-mailbox", "engine/wire/Ingress.lean", "--hub-only",
     "  | some _ => (false, s)",
     "  | some _ => (true, { s with slots := s.slots.set source.val (some value) })", 1,
     "a producer cannot overwrite an owed value"),
    ("sdk-write-wait", "engine/wire/Tcp.lean", "--waits-only",
     "  repeat\n    if (← r.stopped.get) || (← r.writes.isClosed) || (← IO.hasFinished r.done) then return\n    if ← r.writes.trySend ops then return\n    IO.sleep 1",
     "  discard <| (r.writes.send ops).toBaseIO", 1,
     "stop cancels a full-queue Runner.write before handler release"),
    ("lanes-enqueue-wait", "engine/wire/Tcp.lean", "--waits-only",
     "  unless ← enqueue r.events (.lanes p) canceled do return []",
     "  unless ← enqueue r.events (.lanes p) do return []", 1,
     "stop cancels full-queue Runner.lanes before handler release"),
    ("lanes-reply-wait", "engine/wire/Tcp.lean", "--waits-only",
     "    if (← canceled) || (← r.events.isClosed) then return []",
     "    if false then return []", 1,
     "stop cancels admitted unanswered lanes reply before handler release"),
    ("ignore-runner-failure", "engine/wire/Tcp.lean", "--waits-only",
     "(← IO.hasFinished r.done)", "false", 2,
     "runner failure cancels full-queue Runner.write"),
]


def reject_unexpected(transcript, code):
    assert code >= 0, "native process died from a signal"
    assert "PANIC" not in transcript and "uncaught exception" not in transcript, transcript
    failures = re.findall(r"^network runner stopped: (.*)$", transcript, re.M)
    assert all(line == "expected RunnerWaits handler failure" for line in failures), transcript


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", help="local diagnostic subset; default is all eight")
    parser.add_argument("--out", type=Path, default=ROOT / "out/ingress")
    args = parser.parse_args()
    selected = set(args.cases.split(",")) if args.cases else {case[0] for case in CASES}
    assert selected and selected <= {case[0] for case in CASES}, "unknown/empty case filter"
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if args.cases:
        print("LOCAL SUBSET: " + ",".join(sorted(selected)), flush=True)
    os.environ["INGRESS_RUN_DIR"] = str(out / "baseline-data")
    print(run_checked([str(ROOT / ".lake/build/bin/ingress_tcp")], ROOT,
                      out / "baseline.log", timeout=90), end="", flush=True)
    baseline = (out / "baseline.log").read_text()
    reject_unexpected(baseline, 0)
    with tempfile.TemporaryDirectory(prefix="ingress-negative-", dir=os.environ["TMPDIR"]) as temp:
        scratch = Path(temp)
        subprocess.run(["bash", "-c", '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
                        'engine/renderer ops/sync ops/community ops/connection ops/app tests/engine',
                        "ingress-snapshot", str(scratch)], cwd=ROOT, check=True)

        def build(name):
            with (out / f"{name}-build.log").open("w") as log:
                subprocess.run(["systemd-run", "--user", "--scope", "-p", "MemoryMax=48G",
                                "-p", "MemorySwapMax=0", "lake", "build", "ingress_tcp"],
                               cwd=scratch, stdout=log, stderr=subprocess.STDOUT,
                               timeout=600, check=True)

        for name, source, mode, old, new, count, required in CASES:
            if name not in selected:
                continue
            path = scratch / source
            original = path.read_text()
            assert original.count(old) == count, f"{name}: mutation anchor missing/ambiguous"
            try:
                path.write_text(original.replace(old, new))
                build(name)
                os.environ["INGRESS_RUN_DIR"] = str(out / f"{name}-data")
                try:
                    result = subprocess.run([str(scratch / ".lake/build/bin/ingress_tcp"), mode],
                                            cwd=scratch, capture_output=True, text=True, timeout=90)
                except subprocess.TimeoutExpired as exc:
                    (out / f"{name}.log").write_text(str(exc) + "\nTIMEOUT\n")
                    raise
                transcript = result.stdout + result.stderr
                (out / f"{name}.log").write_text(transcript)
                reject_unexpected(transcript, result.returncode)
                failures = set(re.findall(r"^FAIL: (.*)$", transcript, re.M))
                assert result.returncode == 1 and "ingress-tcp:" in transcript and required in failures, \
                    f"{name}: survived or failed for a different reason; see {out}"
                print(f"refused: {name} (compiled; exact runtime assertion)", flush=True)
            finally:
                path.write_text(original)
        build("restored")
        os.environ["INGRESS_RUN_DIR"] = str(out / "restored-data")
        print(run_checked([str(scratch / ".lake/build/bin/ingress_tcp")], scratch,
                          out / "restored.log", timeout=90), end="", flush=True)
        reject_unexpected((out / "restored.log").read_text(), 0)
    print(f"ingress controls: {len(selected)} refused; restored suite passes", flush=True)


if __name__ == "__main__":
    main()
