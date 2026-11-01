"""The real admission implementation must be necessary for its bounds."""
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[2]
# The admission code is a section of the root screen (app/Screen.lean): it
# names no op type and only the app calls it. Its namespace, with what it
# imports, is checked alone, so a mutant costs one small file.
screen = (root / "app/Screen.lean").read_text()
start = screen.index("namespace App.WriteAdmission")
end = screen.index("end App.WriteAdmission") + len("end App.WriteAdmission")
source = "import engine.core.Core\nimport engine.wire.Frame\n\n" + screen[start:end] + "\n"
out = root / "out/write-admission/negative"
out.mkdir(parents=True, exist_ok=True)
(out / "WriteAdmission.lean").write_text(source)
cases = [
    ("unframable", "if !incoming.all fits then", "if false then"),
    ("unbounded-count", "lim.ops < pending.length + incoming.length", "false"),
    ("unbounded-bytes", "lim.bytes < bytes pending + bytes (incoming.map Op.bytes)", "false"),
]
env = dict(os.environ, LEAN_PATH=str(root / ".lake/build/lib/lean"))
baseline = subprocess.run(["lean", str(out / "WriteAdmission.lean")], cwd=root,
                          env=env, capture_output=True, text=True, timeout=60)
(out / "baseline.log").write_text(baseline.stdout + baseline.stderr)
assert baseline.returncode == 0, "baseline laws must compile"
for name, old, new in cases:
    assert source.count(old) == 1, name
    path = out / (name + ".lean")
    path.write_text(source.replace(old, new))
    result = subprocess.run(["lean", str(path)], cwd=root, env=env,
                            capture_output=True, text=True, timeout=60)
    log = result.stdout + result.stderr
    (out / (name + ".log")).write_text(log)
    assert result.returncode != 0 and "error:" in log and "sorry" not in log, (name, log)
    print("admission proof rejects", name, flush=True)
print("all 3 admission mutation controls rejected")
