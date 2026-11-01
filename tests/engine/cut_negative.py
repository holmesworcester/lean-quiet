"""The causal cut's negative controls, in a snapshot (tests/engine/cut.sh).

Each mutant of the trust rule's views must compile into `cut_check` (which
reads the views, not their laws) and fail its specific assertion there;
and the laws must refuse it: building app.community.Proofs fails with an
error inside the theorem named, so the proof, not a neighbour, rejects it.
"""
import pathlib, re, subprocess, sys

root, logs = map(pathlib.Path, sys.argv[1:3])
logs.mkdir(parents=True, exist_ok=True)
VIEWS = "app/community/Commands.lean"
LAWS = "app/community/Proofs.lean"
cases = [
    # A bare per-device counter: an approval counts while its place is at
    # most the head's. A fork signed after the removal at an old place
    # passes it.
    ("bare-counter",
     "(decide (d = f.dev ∧ f.n ≤ m) && behindIn rows x (m - f.n) h)",
     "decide (d = f.dev ∧ f.n ≤ m)",
     "equivocation refused: a fork at a place inside the cut does not readmit",
     "inCut_true"),
    # No cut: every approval is kept, as before the cut.
    ("no-cut",
     "  .list (admission.byDevice.query [c, f.dev]) fun a => usersKeep c x f a.rows",
     "  .pure true",
     "self-readmission refused: bob's own approval does not let his node in",
     "kept_iff"),
    # No chain to the founder: an approval counts if kept, whoever
    # admitted its approver.
    ("no-up",
     "      | some g => counts c k f.up g",
     "      | some _ => .pure true",
     "two-step readmission refused: a user bob admitted after his removal does not let his node in",
     "counts_iff"),
]


def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=3600).returncode


def span(text, theorem):
    """The lines of `theorem NAME` up to the next declaration."""
    lines = text.splitlines()
    start = next(i for i, l in enumerate(lines) if re.match(rf"theorem {re.escape(theorem)}\b", l)) + 1
    end = next((i for i in range(start, len(lines))
                if re.match(r"(theorem|def|/--|section|end |open |namespace )", lines[i])), len(lines))
    return start, end + 1


assert run(["lake", "build", "cut_check"], "baseline-build") == 0
assert run([".lake/build/bin/cut_check", str(logs / "baseline-out")], "baseline") == 0
assert run(["lake", "build", "app.community.Proofs"], "baseline-laws") == 0
laws = (root / LAWS).read_text()
path = root / VIEWS
original = path.read_text()
for name, old, new, assertion, theorem in cases:
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, new))
        assert run(["lake", "build", "cut_check"], name + "-build") == 0, (name, "must compile")
        assert run([".lake/build/bin/cut_check", str(logs / (name + "-out"))], name) != 0, (name, "survived")
        assert "FAIL: " + assertion in (logs / (name + ".log")).read_text(), (name, "wrong failure")
        assert run(["lake", "build", "app.community.Proofs"], name + "-laws") != 0, (name, "laws accept it")
        lo, hi = span(laws, theorem)
        errs = [int(m) for m in re.findall(rf"error: {re.escape(LAWS)}:(\d+):", (logs / (name + "-laws.log")).read_text())]
        assert errs and lo <= min(errs) <= hi, (name, f"first law error {errs[:3]} not inside {theorem} ({lo}-{hi})")
        print(f"refused: {name} (cut_check: {assertion}; laws: {theorem})", flush=True)
    finally:
        path.write_text(original)
assert run(["lake", "build", "cut_check", "app.community.Proofs"], "restored-build") == 0
assert run([".lake/build/bin/cut_check", str(logs / "restored-out")], "restored") == 0
print("cut: all mutants refused, by cut_check and by the laws; restored pass", flush=True)
