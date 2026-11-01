#!/usr/bin/env python3
"""Real retry admission regressions and compiling exact-assertion controls."""
from pathlib import Path
import os
import re
import signal
import subprocess as sp
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "out/retry-admission"
OUT.mkdir(parents=True, exist_ok=True)
CAP = ["systemd-run", "--user", "--scope", "-p", "MemoryMax=48G", "-p", "MemorySwapMax=0"]
sys.path.insert(0, str(ROOT / "tests/vacuity"))
from runtime import run_checked


def command(root, args, name, timeout=600):
    child = sp.Popen(args, cwd=root, text=True, stdout=sp.PIPE,
                     stderr=sp.STDOUT, start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except sp.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (OUT / (name + ".log")).write_text(text + "\nTIMEOUT\n")
        raise
    (OUT / (name + ".log")).write_text(text)
    return child.returncode, text


def build(root, name, target="retry_multiplex", succeeds=True):
    code, text = command(root, CAP + ["lake", "build", target], name + "-build")
    if succeeds:
        assert code == 0, f"{name}: compilation failed; not a successful control"
    else:
        assert code > 0 and "error: engine/wire/RetryOrderLaws.lean:" in text, text


NODE_ORDER = "actual Node retry admission rotates A B C over 40 opportunities"
DURABLE = "authorized late session makes durable catalog progress"
BUSY = "busy socket ticks do not rotate pending retry order"
FALLBACK = "refused candidates retain in-memory fallback positions"
SPLIT = "one scan admits independent sockets without consuming another socket share"
CHURN = "continuing session arrivals cannot overtake an existing pending retry"
SERVICE = "every admitted authorized session receives catalog service"
NATIVE_ORDER = "actual native order rotates all three sessions from either initial position"
ALLOWED = {NODE_ORDER, DURABLE, BUSY, FALLBACK, SPLIT, CHURN, SERVICE, NATIVE_ORDER,
           "both leading sessions repeatedly reach the real TCP receiver, rotated=false",
           "both leading sessions repeatedly reach the real TCP receiver, rotated=true",
           "both serviced peers derive a valid signed root in real SQLite"}


def negative(root, name, required):
    code, text = command(root, [str(root / ".lake/build/bin/retry_multiplex")], name, 90)
    failures = set(re.findall(r"^FAIL: (.+)$", text, re.M))
    assert code == 1 and "retry-multiplex:" in text, (code, text)
    assert not any(x in text.lower() for x in ["panic", "uncaught exception", "segmentation fault", "error:"]), text
    assert required in failures and failures <= ALLOWED, text
    print(f"refused: {name} (compiled; {len(failures)} specific assertions)", flush=True)


def edit(path, old, new):
    text = path.read_text()
    assert text.count(old) == 1, f"ambiguous mutation anchor in {path}"
    path.write_text(text.replace(old, new))


print(run_checked([str(ROOT / ".lake/build/bin/retry_multiplex")], ROOT,
                  OUT / "baseline.log", timeout=90), end="", flush=True)
with tempfile.TemporaryDirectory(prefix="retry-admission-", dir=os.environ["TMPDIR"]) as temp:
    scratch = Path(temp)
    sp.run(["bash", "-c", '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
        'engine/renderer engine/sync app tests/engine', "retry-admission-snapshot", str(scratch)],
        cwd=ROOT, check=True)
    node = scratch / "engine/wire/Node.lean"
    order = scratch / "engine/wire/RetryOrder.lean"
    originals = {p: p.read_text() for p in (node, order)}
    cases = [
        ("old-fixed-order", node,
         "let order := RetryOrder.reconcile (n.conns.map Prod.fst) n.retryOrder",
         "let order := n.conns.map Prod.fst", SERVICE),
        ("newcomers-jump-queue", order,
         "queued.filter live.contains ++ live.filter (fun id => !queued.contains id)",
         "live.filter (fun id => !queued.contains id) ++ queued.filter live.contains", CHURN),
        ("busy-tick-rotation", order,
         "queued.filter (fun id => !sent.contains id) ++ queued.filter sent.contains",
         "if sent.isEmpty then queued.drop 1 ++ queued.take 1 else\n  queued.filter (fun id => !sent.contains id) ++ queued.filter sent.contains", BUSY),
        ("refused-fallback-advance", node,
         "then { next with sweeps := before } else next", "then next else next", FALLBACK),
        ("overbook-socket", order,
         "if candidate && !claimed.contains a then", "if candidate then", FALLBACK),
    ]
    for name, path, old, new, required in cases:
        try:
            edit(path, old, new)
            build(scratch, name)
            negative(scratch, name, required)
        finally:
            for p, text in originals.items():
                p.write_text(text)
    try:
        edit(order, "queued.filter (fun id => !sent.contains id) ++ queued.filter sent.contains", "queued")
        build(scratch, "no-progress-kernel", "engine.wire.RetryOrderLaws", succeeds=False)
        print("refused: no-progress-kernel (unchanged RetryOrderLaws)", flush=True)
    finally:
        for p, text in originals.items():
            p.write_text(text)
    build(scratch, "restored")
    print(run_checked([str(scratch / ".lake/build/bin/retry_multiplex")], scratch,
                      OUT / "restored.log", timeout=90), end="", flush=True)
