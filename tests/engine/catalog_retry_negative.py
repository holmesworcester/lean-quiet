#!/usr/bin/env python3
"""Lost-control/data regression, plus a compiling disabled-retry mutant."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "out/catalog-retry"
sys.path.insert(0, str(ROOT / "tests/vacuity"))
from runtime import run_checked


def build(root: Path, name: str) -> None:
    with (OUT / f"{name}-build.log").open("w") as log:
        subprocess.run(
            ["systemd-run", "--user", "--scope", "-p", "MemoryMax=48G", "-p",
             "MemorySwapMax=0", "lake", "build", "catalog_retry"],
            cwd=root, stdout=log, stderr=subprocess.STDOUT, timeout=600, check=True)


OUT.mkdir(parents=True, exist_ok=True)
print(run_checked([str(ROOT / ".lake/build/bin/catalog_retry")], ROOT,
                  OUT / "baseline.log", timeout=180), end="", flush=True)
with tempfile.TemporaryDirectory(prefix="catalog-retry-", dir=os.environ["TMPDIR"]) as temp:
    scratch = Path(temp)
    subprocess.run(
        ["bash", "-c", '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
         'engine/renderer ops/sync ops/community ops/connection ops/app tests/engine',
         "catalog-snapshot", str(scratch)], cwd=ROOT, check=True)
    path = scratch / "engine/wire/Node.lean"
    original = path.read_text()
    anchor = "  let some catalog := x.catalog | return (n, {})"
    assert original.count(anchor) == 1, "disabled-sweep anchor missing"
    path.write_text(original.replace(anchor,
        "  let some catalog := (none : Option (Catalog m)) | return (n, {})"))
    build(scratch, "disabled-sweep")
    result = subprocess.run([str(scratch / ".lake/build/bin/catalog_retry")], cwd=scratch,
                            capture_output=True, text=True, timeout=180)
    transcript = result.stdout + result.stderr
    (OUT / "disabled-sweep.log").write_text(transcript)
    assert result.returncode != 0, "disabled retry survived"
    assert "PANIC" not in transcript, "mutant panicked instead of reaching the assertion"
    assert "FAIL: target arrives despite lost opening, all controls lost, and continuing producers" in transcript
    print("refused: disabled-sweep (compiled, target delivery assertion failed)", flush=True)
    path.write_text(original)
    build(scratch, "restored")
    print(run_checked([str(scratch / ".lake/build/bin/catalog_retry")], scratch,
                      OUT / "restored.log", timeout=180), end="", flush=True)
