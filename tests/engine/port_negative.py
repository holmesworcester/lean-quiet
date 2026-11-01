"""Runtime mutations in an isolated snapshot, with a positive baseline and
specific failing assertions; compiler failures are never accepted as runtime
refusals. Proof mutations are separate: the mutant must fail to check inside
the one named theorem that proves the property of the code that runs."""
import pathlib, re, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:3])
group = sys.argv[3]
logs.mkdir(parents=True, exist_ok=True)
cases = {
    "people": [
        ("false-exact-count", "app/Screen.lean",
         "    return (.people n (all && n < 999), deps)",
         "    return (.people n true, deps)",
         "incomplete scan is marked even when the visible unique count is small"),
    ],
    "tree": [
        ("no-range-cuts", "engine/sync/Round.lean",
         "def runLen (n : Nat) : Nat := (n + P.fan - 1) / P.fan",
         "def runLen (n : Nat) : Nat := n + 0 * P.fan",
         "non-leaf 64: logarithmic depth gives exactly the missing ids"),
        ("drop-wants", "engine/sync/Round.lean",
         "     .want (xs.filter fun i => !named ident x i)]",
         "     .want []]",
         "non-leaf 64: logarithmic depth gives exactly the missing ids"),
    ],
}[group]
# Mutants a law of the running code rejects: the module no longer checks,
# with an error inside that theorem (not a parse or import error elsewhere).
proof_cases = {
    "people": [
        # Dropping presentW's `limit := some m` makes the window read every
        # admission; PeopleLaws.presentW_lists_eq (the window reads one list
        # of at most m admissions) sits in the same module and rejects it.
        ("unbounded-admissions", "app/community/Screen.lean",
         "  let a ← admission.all.read [c] (limit := some m)",
         "  let a ← admission.all.read [c]",
         "presentW_lists_eq"),
    ],
    "tree": [],
}[group]
target = "people_reader" if group == "people" else "claim_tree"
def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode
assert run(["lake", "build", target], "baseline-build") == 0
assert run([".lake/build/bin/" + target], "baseline") == 0
for name, source, old, new, assertion in cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, new))
        assert run(["lake", "build", target], name + "-build") == 0, (name, "must compile")
        assert run([".lake/build/bin/" + target], name) != 0, (name, "survived")
        assert "FAIL: " + assertion in (logs / (name + ".log")).read_text(), (name, "wrong failure")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
for name, source, old, new, theorem in proof_cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    begin = original.index("theorem " + theorem + " ")
    end = original.find("\ntheorem ", begin)
    first = original[:begin].count("\n") + 1
    last = original[:end].count("\n") + 1 if end >= 0 else original.count("\n") + 1
    try:
        path.write_text(original.replace(old, new))
        assert run(["lake", "env", "lean", source], name + "-proof") != 0, (name, "proof mutant survived")
        out = (logs / (name + "-proof.log")).read_text()
        errors = [int(n) for n in re.findall(re.escape(pathlib.Path(source).name) + r":(\d+):\d+: error", out)]
        assert any(first <= n < last for n in errors), (name, "no error inside " + theorem, errors)
        print("refused:", name, "by the proof of running code (" + theorem + ")", flush=True)
    finally:
        path.write_text(original)
assert run(["lake", "build", target], "restored-build") == 0
assert run([".lake/build/bin/" + target], "restored") == 0
print(group + ": all mutants refused; restored pass", flush=True)
