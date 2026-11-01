#!/usr/bin/env python3
"""Catalog delivery and initialization regressions with compiling controls."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "out/catalog-retry"
sys.path.insert(0, str(ROOT / "tests/vacuity"))
from runtime import run_checked
sys.path.insert(0, str(ROOT / "tests"))
import mutants


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
    scratch = Path(temp) / "base"
    subprocess.run(
        ["bash", "-c", '. tests/snapshot.sh; snapshot "$1" engine/core engine/wire '
         'engine/renderer engine/sync app tests/engine',
         "catalog-snapshot", str(scratch)], cwd=ROOT, check=True)
    cases = [
        ("disabled-sweep", "engine/wire/Node.lean",
         "  let some catalog := x.catalog | return (n, {})",
         "  let some catalog := (none : Option (Catalog m)) | return (n, {})",
         "FAIL: target arrives despite lost opening, all controls lost, and continuing producers"),
        ("open-takes-writer", "engine/core/Sqlite.lean",
         '  db.exec schemaCore\n  let version ← db.query "SELECT version FROM catalog_version WHERE version = 1" #[]\n  if version.isEmpty then db.exec catalogMigration',
         "  db.exec schema",
         "FAIL: initialized database opens without acquiring the held writer lock"),
    ]
    def control(case, work):
        name, source, anchor, mutation, expected = case
        path = work / source
        original = path.read_text()
        assert original.count(anchor) == 1, f"{name}: mutation anchor missing"
        path.write_text(original.replace(anchor, mutation))
        build(work, name)
        result = subprocess.run([str(work / ".lake/build/bin/catalog_retry")], cwd=work,
                                capture_output=True, text=True, timeout=180)
        transcript = result.stdout + result.stderr
        (OUT / f"{name}.log").write_text(transcript)
        assert result.returncode != 0, f"{name}: mutation survived"
        assert "PANIC" not in transcript and "uncaught exception" not in transcript, \
            f"{name}: crashed instead of reaching the assertion"
        assert expected in transcript, f"{name}: failed for an unrelated reason"
        return f"refused: {name} (compiled, actual regression assertion failed)"

    mutants.each(scratch, cases, control)
