#!/usr/bin/env python3
"""Break production definitions, require rejection, and restore in finally.

Run without concurrent builds in this worktree. Logs identify each mutation.
The final build restores the checked artifacts as well as the source files.
"""
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
os.environ["ELAN_HOME"] = os.environ.get("ELAN_HOME", "/mnt/storage/elan")
os.environ["PATH"] = os.environ["ELAN_HOME"] + "/bin:" + os.environ["PATH"]
OUT = ROOT / "out/safe/negative"
OUT.mkdir(parents=True, exist_ok=True)

cases = [
    ("target-minimum", "SafeFrame", "(48 * dpi + 159) / 160", "(48 * dpi) / 160"),
    ("content-bounds", "Safe", "i.w - x - n.right", "i.w + 1"),
    ("reserved-disjoint", "Safe", "i.w, r.y⟩", "i.w, r.y + 1⟩"),
    ("target-safe", "Safe", "r.Inside (content i) ∧ 0 < r.w", "0 < r.w"),
    ("target-witness", "Safe", "⟨48, 200, 126, 126⟩", "⟨48, 100, 126, 126⟩"),
    ("edge-colour", "SafeFrame", "⟨reserved i edge, edgeColour screen theme edge⟩", "⟨reserved i edge, 0⟩"),
    ("covering-table", "Occlusion", "∧ MayCover upper lower inert", "∧ True"),
    ("overlay-safe", "Occlusion", "upper.rect.Inside (content i) ∧ ", ""),
    ("modal-inert", "Occlusion", "!modal || decide (layer = .surface)", "true"),
    ("toast-safe", "Toast", "Occlusion.place i card ⟨.page, view⟩ false focused", "some card"),
    ("toast-view", "Toast", "card.rect.Inside view ∧ ", ""),
    ("toast-size", "Toast", "key ≤ w ∧ key ≤ h", "0 ≤ w ∧ 0 ≤ h"),
    ("toast-expiry", "Toast", "if now < deadline then", "if true then"),
    ("toast-dismissal", "Toast", "pending.bind fun", "(pending.or (some (\"stale\", now + 1))).bind fun"),
    ("toast-visible", "Toast", "def life : Nat := 3000", "def life : Nat := 0"),
    ("toast-witness", "Toast", "view.x + (view.w - w) / 2", "view.x + (view.w - w) / 2 + 1"),
    ("resize-fresh", "App", "W := safe.w, Hs := window.h", "W := s.W, Hs := s.Hs"),
    ("insets-fresh", "App", "window := window, W := safe.w", "window := s.window, W := safe.w"),
]

def run(cmd, log):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT / (log + ".log")).write_text(p.stdout)
    return p

assert run(["lake", "build", "Quiet.SafeLaws"], "baseline").returncode == 0
try:
    for name, module, before, after in cases:
        path = ROOT / "Quiet" / (module + ".lean")
        original = path.read_text()
        assert before in original, (name, "mutation anchor missing")
        try:
            path.write_text(original.replace(before, after))
            cmd = (["lake", "build", "Quiet.SafeLaws"] if module == "App" else
                   ["lake", "env", "lean", str(path)])
            result = run(cmd, name)
            assert result.returncode != 0 and "error:" in result.stdout, (name, "mutation survived")
            print("rejected", name, flush=True)
        finally:
            path.write_text(original)
    path = ROOT / "android/twin/java/com/holmes/leanquiet/BarState.java"
    original = path.read_text()
    for name, before, after in [
        ("bars-recreation", "window = new WeakReference<>(next);", "choice = null; window = new WeakReference<>(next);"),
        ("bars-old-window", "if (window.get() == current) apply(current);", "apply(current);"),
        ("bars-old-choice", "apply(current);\n    });", "current.paintBars(next);\n    });"),
    ]:
        try:
            assert before in original
            path.write_text(original.replace(before, after))
            result = run(["tests/bar_state.sh"], name)
            assert result.returncode != 0 and "AssertionError" in result.stdout, (name, "mutation survived")
            print("rejected", name, flush=True)
        finally:
            path.write_text(original)
    path = ROOT / "Quiet/App.lean"
    original = path.read_text()
    for name, before, after in [
        ("reserved-touch-path", "if (Safe.target i ⟨x, sy, 1, 1⟩).isNone then return", "if (Safe.target i ⟨x, sy, 1, 1⟩).isNone && false then return"),
        ("toast-paint-path", "let r0 := over + (placed.rect.y - g.top) + (if s.page == .chat then g.shift else 0)", "let r0 := over"),
        ("stale-ime-event", "| .ime _ => decide (sc.size ≥ 8)", "| .ime _ => false"),
        ("modal-send", "if !Occlusion.active (← get).sheet.isSome .page then return true", "if false then return true"),
    ]:
        try:
            assert before in original
            path.write_text(original.replace(before, after))
            assert run(["lake", "build", "safe"], name + "-build").returncode == 0
            result = run([".lake/build/bin/safe", str(OUT / name), "--no-renders"], name)
            assert result.returncode != 0 and "FAIL" in result.stdout, (name, "mutation survived")
            print("rejected", name, flush=True)
        finally:
            path.write_text(original)
    path = ROOT / "Quiet/SafeFrame.lean"
    original = path.read_text()
    try:
        before = "1.05 / (l + 0.05) ≥ (l + 0.05) / 0.05"
        assert before in original
        path.write_text(original.replace(before, "1.05 / (l + 0.05) ≤ (l + 0.05) / 0.05"))
        assert run(["lake", "build", "safe"], "icon-polarity-build").returncode == 0
        result = run([".lake/build/bin/safe", str(OUT / "icon-polarity"), "--no-renders"], "icon-polarity")
        assert result.returncode != 0 and "FAIL" in result.stdout
        print("rejected icon-polarity", flush=True)
    finally:
        path.write_text(original)
finally:
    assert run(["lake", "build", "safe"], "restored").returncode == 0
    assert run(["tests/bar_state.sh"], "bars-restored").returncode == 0
print(f"{len(cases) + 8} mutations rejected; sources and build restored")
