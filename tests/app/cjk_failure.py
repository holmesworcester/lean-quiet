#!/usr/bin/env python3
"""An actual CJK runner error must exit, even with writer tasks alive."""
from pathlib import Path
import subprocess

out = Path("out/cjk-failure")
out.mkdir(parents=True, exist_ok=True)
args = [".lake/build/bin/cjk_scroll", str(out / "runtime"),
        "out/cjk/corpus.txt", "--fail-after-writer-start"]
try:
    result = subprocess.run(args, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, timeout=15)
except subprocess.TimeoutExpired as error:
    output = error.stdout or b""
    if isinstance(output, bytes):
        output = output.decode(errors="replace")
    (out / "failure.log").write_text(output + "\nTIMEOUT: error teardown hung\n")
    raise
(out / "failure.log").write_text(result.stdout)
assert result.returncode == 1, (result.returncode, result.stdout)
assert "injected CJK failure after writer startup" in result.stdout, result.stdout
assert not any(word in result.stdout.lower() for word in
               ["segmentation fault", "panic", "assertion violation"]), result.stdout
print("CJK failure: real writer tasks cannot hide the intended error or its exit status")
