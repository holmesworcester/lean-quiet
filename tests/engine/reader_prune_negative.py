#!/usr/bin/env python3
"""Require real Reader/SQLite/pruner success and a compiling early-ack failure."""
from pathlib import Path
import subprocess
import shutil
import sys

root, logs = map(Path, sys.argv[1:])
logs.mkdir(parents=True, exist_ok=True)


def run(args, name):
    try:
        p = subprocess.run(args, cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, timeout=180)
    except subprocess.TimeoutExpired as e:
        output = e.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        (logs / (name + ".log")).write_text(output + "\nTIMEOUT\n")
        raise
    (logs / (name + ".log")).write_text(p.stdout)
    return p


def build(name):
    p = run(["systemd-run", "--user", "--scope", "-p", "MemoryMax=48G", "-p",
             "MemorySwapMax=0", "lake", "build", "reader_prune_rollback"], name)
    assert p.returncode == 0, (name, "must compile")


def exercise(name, good):
    # Preserve each real SQLite database before the scratch snapshot is deleted,
    # including assertion failures, crashes and timeouts.
    try:
        p = run([str(root / ".lake/build/bin/reader_prune_rollback")], name)
    finally:
        runtime = root / "out/reader-prune/runtime"
        if runtime.exists():
            shutil.copytree(runtime, logs / (name + "-db"), dirs_exist_ok=True)
    assert (logs / (name + "-db/reader.db")).is_file(), (name, "missing database evidence")
    assert not any(marker in p.stdout.lower() for marker in
                   ["panic", "uncaught exception", "segmentation fault", "assertion violation"]), (name, "invalid runtime failure")
    if good:
        assert p.returncode == 0 and "reader_prune_rollback: 9 passed, 0 failed" in p.stdout, (name, p.stdout)
    else:
        assert p.returncode == 1 and "reader_prune_rollback: 5 passed, 4 failed" in p.stdout, (name, p.stdout)
        assert "FAIL: healthy reader retry after actual pruning refreshes the cached count to 41" in p.stdout
        assert "remaining=0, retry=(some 40)" in p.stdout


build("baseline-build")
exercise("baseline", True)
source = root / "app/Screen.lean"
original = source.read_text()
ack = "    sh.seen.modify (fun _ => top)\n"
early = "    -- mark the dirty and the wanted wants those reads name, through the\n"
assert original.count(ack) == 1 and original.count(early) == 1, "missing unique acknowledgement anchors"
try:
    source.write_text(original.replace(ack, "").replace(early, ack + early))
    build("early-ack-build")
    exercise("early-ack", False)
    print("rejected: journal acknowledgement before successful reader COMMIT", flush=True)
finally:
    source.write_text(original)
build("restored-build")
exercise("restored", True)
print("reader prune: 9 actual SQL checks, compiling early-ack control and restored source passed", flush=True)
