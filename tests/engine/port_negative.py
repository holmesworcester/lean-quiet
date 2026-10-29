"""Runtime mutations in an isolated snapshot, with a positive baseline and
specific failing assertions; compiler failures are never accepted."""
import pathlib, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:3])
group = sys.argv[3]
logs.mkdir(parents=True, exist_ok=True)
cases = {
    "people": [
        ("unbounded-admissions", "ops/community/profile/View.lean",
         "  let a ← admission.all.read [c] (limit := some m)",
         "  let a ← admission.all.read [c]",
         "header asks for only the newest 1024 admissions"),
        ("false-exact-count", "ops/app/Reader.lean",
         "    return (.people n (all && n < 999), deps)",
         "    return (.people n true, deps)",
         "incomplete scan is marked even when the visible unique count is small"),
    ],
    "tree": [
        ("no-range-cuts", "ops/sync/Round.lean",
         "def runLen (n : Nat) : Nat := (n + P.fan - 1) / P.fan",
         "def runLen (n : Nat) : Nat := n + 0 * P.fan",
         "non-leaf 64: logarithmic depth gives exactly the missing ids"),
        ("drop-wants", "ops/sync/Round.lean",
         "     .want (xs.filter fun i => !named ident x i)]",
         "     .want []]",
         "non-leaf 64: logarithmic depth gives exactly the missing ids"),
    ],
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
assert run(["lake", "build", target], "restored-build") == 0
assert run([".lake/build/bin/" + target], "restored") == 0
print(group + ": all mutants refused; restored pass", flush=True)
