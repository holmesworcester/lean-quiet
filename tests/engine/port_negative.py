"""Mutations in an isolated snapshot, with a positive baseline. A runtime
case must compile and fail its specific assertion; a case that names a law
(a sixth field) must be refused by that law, its build failing with an
error inside the law's declaration. Any other compiler failure is never
accepted."""
import pathlib, re, subprocess, sys
root, logs = map(pathlib.Path, sys.argv[1:3])
group = sys.argv[3]
logs.mkdir(parents=True, exist_ok=True)
cases = {
    "people": [
        # The header's cost law states the bound in the same module as the
        # view: removing the limit is refused by the proof, before any run.
        ("unbounded-admissions", "app/community/Screen.lean",
         "  let a ← admission.all.read [c] (limit := some m)",
         "  let a ← admission.all.read [c]",
         "header asks for only the newest 1024 admissions", "presentW_lists_eq"),
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
target = "people_reader" if group == "people" else "claim_tree"
def run(args, name):
    with (logs / (name + ".log")).open("w") as out:
        return subprocess.run(args, cwd=root, stdout=out, stderr=subprocess.STDOUT, timeout=600).returncode
assert run(["lake", "build", target], "baseline-build") == 0
assert run([".lake/build/bin/" + target], "baseline") == 0
def law_lines(text, law):
    """The lines (1-based) of the declaration `theorem law`."""
    lines = text.split("\n")
    start = next(i for i, l in enumerate(lines) if re.match(rf"^theorem {re.escape(law)}\b", l))
    end = next((i for i in range(start + 1, len(lines))
                if re.match(r"^(theorem|def|lemma|structure|inductive|abbrev|instance|/--|/-!|end |section|namespace)", lines[i])),
               len(lines))
    return range(start + 1, end + 1)
for name, source, old, new, assertion, *law in cases:
    path = root / source
    original = path.read_text()
    assert original.count(old) == 1, (name, "mutation target missing")
    try:
        path.write_text(original.replace(old, new))
        if law:
            assert run(["lake", "build", target], name + "-build") != 0, (name, "survived its law")
            log = (logs / (name + "-build.log")).read_text()
            lines = law_lines(original, law[0])
            hits = [int(n) for n in re.findall(rf"^error: {re.escape(source)}:(\d+):", log, re.M)]
            assert any(n in lines for n in hits), (name, "refused, but not by " + law[0], hits)
            print("refused by " + law[0] + ":", name, flush=True)
            continue
        assert run(["lake", "build", target], name + "-build") == 0, (name, "must compile")
        assert run([".lake/build/bin/" + target], name) != 0, (name, "survived")
        assert "FAIL: " + assertion in (logs / (name + ".log")).read_text(), (name, "wrong failure")
        print("refused:", name, flush=True)
    finally:
        path.write_text(original)
assert run(["lake", "build", target], "restored-build") == 0
assert run([".lake/build/bin/" + target], "restored") == 0
print(group + ": all mutants refused; restored pass", flush=True)
