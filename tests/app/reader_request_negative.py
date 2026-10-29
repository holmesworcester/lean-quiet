"""Force the old request/generation race in the actual SQLite reader pass.

Run in an idle worktree. Preserve logs, restore source and rebuild even when
the control fails, and require the intended window assertion, not any failure.
"""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[2]
logs = root / "out/app-lifecycle/reader-request-negative"
logs.mkdir(parents=True, exist_ok=True)
source = root / "ops/app/Reader.lean"
original = source.read_bytes()
anchor = "  let (gen, wants) ← sh.request.get\n  afterSnapshot\n"
mutant = anchor + "  let gen ← sh.generation\n"
assert original.decode().count(anchor) == 1, "reader sampling seam missing"


def run(args, name):
    result = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=300)
    output = result.stdout + result.stderr
    (logs / (name + ".log")).write_text(output)
    return result.returncode, output


def build(name):
    code, _ = run(["lake", "build", "app_lifecycle"], name)
    assert code == 0, name + ": build failed; not a runtime control result"


command = [".lake/build/bin/app_lifecycle", str(logs / "db"), "reader-request"]
build("baseline-build")
assert run(command, "baseline")[0] == 0, "baseline regression failed"
try:
    source.write_text(original.decode().replace(anchor, mutant, 1))
    build("torn-generation-build")
    code, output = run(command, "torn-generation")
    assert code == 1, "torn-generation control did not fail normally"
    assert "FAIL: new window arrives on next pass without another change" in output, output
    assert "FAIL: periodic fallback retains the requested message window" in output, output
    print("detected torn-generation: next pass and periodic fallback both miss the new window", flush=True)
finally:
    source.write_bytes(original)
    build("restored-build")
    assert run(command, "restored")[0] == 0, "restored regression failed"
print("reader request: baseline and restored pass; negative control detected", flush=True)
