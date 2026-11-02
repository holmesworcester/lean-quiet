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
        ("both", "android-photo", "", ["run android:photo-e2e", "run android:photo-lifecycle-e2e"], 0),
        ("picker-fails", "android-photo", "android:photo-e2e", ["run android:photo-e2e"], 1),
        ("lifetime-fails", "android-photo", "android:photo-lifecycle-e2e",
         ["run android:photo-e2e", "run android:photo-lifecycle-e2e"], 1),
        ("owned-direct", "owned-input", "", ["run test:owned-input"], 0),
        ("owned-fails", "owned-input", "test:owned-input", ["run test:owned-input"], 1),
        ("owned-android", "android-owned-input", "", ["run android:owned-input-e2e"], 0),
        ("app-with-owned", "app", "", ["run test:app", "run windows:input", "run test:owned-input"], 0),
        ("app-fails", "app", "test:app", ["run test:app"], 1),
        ("windows-fails", "app", "windows:input", ["run test:app", "run windows:input"], 1),
        ("app-owned-fails", "app", "test:owned-input", ["run test:app", "run windows:input", "run test:owned-input"], 1),
        ("clean-room", "make:clean-room", "", ["run make:clean-room"], 0),
        ("clean-room-fails", "make:clean-room", "make:clean-room", ["run make:clean-room"], 1),
        ("make-assets", "make:assets", "", ["run make:assets-test"], 0),
        ("make-demo", "make:demo", "", ["run make:demo-e2e", "run make:demo-negative"], 0),
        ("make-demo-e2e-fails", "make:demo", "make:demo-e2e", ["run make:demo-e2e"], 1),
        ("make-demo-negative-fails", "make:demo", "make:demo-negative",
         ["run make:demo-e2e", "run make:demo-negative"], 1),
        ("make-assets-fails", "make:assets", "make:assets-test", ["run make:assets-test"], 1),
        ("make-verify", "make:verify", "", ["run make:verify-test"], 0),
        ("make-verify-fails", "make:verify", "make:verify-test", ["run make:verify-test"], 1),
    ]
    for name, part, fail, expected, code in cases:
        calls = work / (name + ".calls")
        env = dict(os.environ, PATH=str(work / "bin") + os.pathsep + os.environ["PATH"],
                   DISPATCH_CALLS=str(calls), DISPATCH_FAIL=fail)
        result = subprocess.run(["bash", "ci/local.sh", part], cwd=work,
                                env=env, capture_output=True, text=True, timeout=30)
        actual = calls.read_text().splitlines() if calls.exists() else []
        (LOGS / (name + ".log")).write_text(result.stdout + result.stderr + repr(actual) + "\n")
        assert (result.returncode, actual) == (code, expected), (name, result.returncode, actual)
        print("CI dispatcher:", name, "passed")
