#!/usr/bin/env python3
"""Exercise the actual CI dispatcher without starting provisioned devices."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "out/ci-driver"
LOGS.mkdir(parents=True, exist_ok=True)

with tempfile.TemporaryDirectory(prefix="quiet-ci-driver-", dir=os.environ.get("TMPDIR", "/mnt/storage/holmes-tmp")) as tmp:
    work = Path(tmp)
    (work / "ci").mkdir()
    (work / "bin").mkdir()
    shutil.copy2(ROOT / "ci/local.sh", work / "ci/local.sh")
    mise = work / "bin/mise"
    mise.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$DISPATCH_CALLS"\n'
                    '[ "$*" != "run $DISPATCH_FAIL" ]\n')
    mise.chmod(0o755)
    cases = [
        ("both", "", ["run android:photo-e2e", "run android:photo-lifecycle-e2e"], 0),
        ("picker-fails", "android:photo-e2e", ["run android:photo-e2e"], 1),
        ("lifetime-fails", "android:photo-lifecycle-e2e",
         ["run android:photo-e2e", "run android:photo-lifecycle-e2e"], 1),
    ]
    for name, fail, expected, code in cases:
        calls = work / (name + ".calls")
        env = dict(os.environ, PATH=str(work / "bin") + os.pathsep + os.environ["PATH"],
                   DISPATCH_CALLS=str(calls), DISPATCH_FAIL=fail)
        result = subprocess.run(["bash", "ci/local.sh", "android-photo"], cwd=work,
                                env=env, capture_output=True, text=True, timeout=30)
        actual = calls.read_text().splitlines() if calls.exists() else []
        (LOGS / (name + ".log")).write_text(result.stdout + result.stderr + repr(actual) + "\n")
        assert (result.returncode, actual) == (code, expected), (name, result.returncode, actual)
        print("CI dispatcher:", name, "passed")
