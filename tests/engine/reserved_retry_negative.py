#!/usr/bin/env python3
"""Actual TCP retry/metadata gates and specific compiling failure controls.

Every variant lives in a private copied build tree, never the worktree under
test. A missing anchor or compile failure does not count as a runtime kill.
"""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "out/reserved-retry"
sys.path.insert(0, str(ROOT / "tests/vacuity"))
from runtime import run_checked


def build(root: Path, name: str, target="reserved_retry", succeeds=True):
    with (OUT / f"{name}-build.log").open("w") as log:
        result = subprocess.run(
            ["systemd-run", "--user", "--scope", "-p", "MemoryMax=48G",
             "-p", "MemorySwapMax=0", "lake", "build", target], cwd=root,
            stdout=log, stderr=subprocess.STDOUT, timeout=600)
    if succeeds:
        assert result.returncode == 0, f"{name} did not compile"
    else:
        assert result.returncode != 0, f"{name} survived the unchanged bound"


DELIVERY = "reserved retry crosses actual TCP despite continuously refused normal data"
PREPARED = "prepared retry does not advance durable cursor before native write"
ALLOWED = {
    DELIVERY, PREPARED,
    "closing before writer completion preserves retry position",
    "lost target receives at least three actual native wire attempts",
    "ordinary wants and new posting continue until target delivery",
    "actual loop services flooded peer frames during retry recovery",
    "received target settles to the same valid view input",
    "actual completed writer attempts persist peer retry progress",
}


def negative(root: Path, name: str, required: str):
    result = subprocess.run([str(root / ".lake/build/bin/reserved_retry")],
                            cwd=root, capture_output=True, text=True, timeout=90)
    transcript = result.stdout + result.stderr
    (OUT / f"{name}.log").write_text(transcript)
    failures = set(re.findall(r"^FAIL: (.+)$", transcript, re.M))
    assert result.returncode == 1 and "PANIC" not in transcript, transcript
    assert "reserved-retry:" in transcript and required in failures, transcript
    assert failures <= ALLOWED, f"unrelated mutant failures: {failures - ALLOWED}"
    print(f"refused: {name} (compiled; {len(failures)} expected assertions)", flush=True)


def edit(path: Path, old: str, new: str):
    source = path.read_text()
    assert source.count(old) == 1, f"missing/ambiguous mutation anchor in {path.name}"
    path.write_text(source.replace(old, new))


OUT.mkdir(parents=True, exist_ok=True)
print(run_checked([str(ROOT / ".lake/build/bin/reserved_retry")], ROOT,
                  OUT / "baseline.log", timeout=90), end="", flush=True)
with tempfile.TemporaryDirectory(prefix="reserved-retry-", dir=os.environ["TMPDIR"]) as temp:
    scratch = Path(temp)
    subprocess.run(
        ["bash", "-c", '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
         'engine/renderer ops/sync ops/community ops/connection ops/app tests/engine',
         "reserved-snapshot", str(scratch)], cwd=ROOT, check=True)
    node = scratch / "engine/wire/Node.lean"
    tcp = scratch / "engine/wire/Tcp.lean"
    conn = scratch / "ops/sync/Conn.lean"
    originals = {p: p.read_text() for p in (node, tcp, conn)}

    def restore():
        for path, source in originals.items():
            path.write_text(source)

    edit(tcp, "retryRoom := ← retryRooms st.socks", "retryRoom := fun _ => some 0")
    build(scratch, "no-reservation")
    negative(scratch, "no-reservation", DELIVERY)
    restore()

    edit(node, "if !x.deferredRetries || offered.isNone then store.save peer cursor",
         "store.save peer cursor")
    build(scratch, "early-cursor")
    negative(scratch, "early-cursor", PREPARED)
    restore()

    edit(tcp, "(true, { o with lanes := q'.ordinary, dropped := if ok then o.dropped else o.dropped + 1 })",
         "(ok, { o with lanes := q'.ordinary, dropped := if ok then o.dropped else o.dropped + 1 })")
    edit(tcp, "unless ordinary.isEmpty do discard <| s.push cfg ordinary",
         "unless ordinary.isEmpty do\n        unless ← s.push cfg ordinary do over := s.id :: over")
    build(scratch, "overflow-closes")
    negative(scratch, "overflow-closes", DELIVERY)
    restore()

    edit(tcp, "retry := if usedRetry then o.retry.sent true else o.retry", "retry := o.retry")
    build(scratch, "missing-completion")
    negative(scratch, "missing-completion", DELIVERY)
    restore()

    edit(conn, "(first.filter c.owing.contains).eraseDups.take 1",
         "(first.filter c.owing.contains).eraseDups")
    build(scratch, "unbounded-hot", target="ops.sync.ServeLaws", succeeds=False)
    log = (OUT / "unbounded-hot-build.log").read_text()
    assert "ops/sync/ServeLaws.lean:" in log and "error:" in log
    print("refused: unbounded-hot (unchanged hot-count proof)", flush=True)
    restore()

    build(scratch, "restored")
    print(run_checked([str(scratch / ".lake/build/bin/reserved_retry")], scratch,
                      OUT / "restored.log", timeout=90), end="", flush=True)
