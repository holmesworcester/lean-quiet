#!/usr/bin/env python3
"""The README's theorem links, from Lean's own declaration ranges.

Every theorem the audit lists (`#print axioms` in tests/Axioms.lean) is
looked up in the built environment (`findDeclarationRanges?`), and linked
to its file and lines: from its docstring through its statement, not its
proof. The assumptions the README names (`ASSUMED`) are linked whole,
definition included.

The README names a theorem as a shortcut reference, [`no_impersonation`],
by its full name or any suffix of it that names one of these; the link
definitions go in the block between the proof-links markers at its end.

  ci/proof-links.py           rewrite the block
  ci/proof-links.py --check   fail if the block is stale, a reference
                              names no audited theorem, or the README's
                              "All N rest on" count is not the audit's

Needs the tree built (tests/check.sh builds it).
"""
import os, re, subprocess, sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUDIT = os.path.join(TOP, "tests", "Axioms.lean")
README = os.path.join(TOP, "README.md")
BEGIN = "<!-- proof-links: written by ci/proof-links.py; do not edit -->"
END = "<!-- /proof-links -->"
# How many theorems the audit lists, counted as they are probed.
AUDITED = [0]
# Definitions the theorems take as hypotheses.
ASSUMED = ["Community.Unforgeable", "Engine.CollisionFree", "Engine.Distinct",
           "Connection.Noise.Suite.Good", "Connection.Keys.Good",
           "Community.Merkle.NoSecondPreimage"]

PROBE = """open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in %s do
    let n := s.toName
    let mod := match env.getModuleIdxFor? n with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    match ← findDeclarationRanges? n with
    | some r => IO.println s!"{s}\\t{mod}\\t{r.range.pos.line}\\t{r.selectionRange.pos.line}\\t{r.range.endPos.line}"
    | none => IO.println s!"{s}\\t{mod}\\t0\\t0\\t0"
"""


def audit():
    if not os.path.exists(AUDIT):
        sys.exit("proof-links: no axiom audit (tests/Axioms.lean)")
    text = open(AUDIT).read()
    return (re.findall(r"^import (\S+)", text, re.M),
            re.findall(r"^#print axioms (\S+)", text, re.M))


def ranges():
    imports, names = audit()
    AUDITED[0] += len(names)
    names = names + ASSUMED
    out = os.path.join(TOP, "out", "proof-links")
    os.makedirs(out, exist_ok=True)
    probe = os.path.join(out, "audit.lean")
    with open(probe, "w") as f:
        f.write("import Lean\n" + "".join(f"import {m}\n" for m in imports))
        f.write(PROBE % ("[" + ", ".join(f'"{n}"' for n in names) + "]"))
    r = subprocess.run(["lake", "env", "lean", probe], cwd=TOP, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"proof-links: probing the audit failed (is the tree built?)\n{r.stdout}{r.stderr}")
    found = {}
    for line in r.stdout.splitlines():
        name, mod, start, sel, end = line.split("\t")
        path = os.path.join(*mod.split(".")) + ".lean"
        if mod == "?" or sel == "0" or not os.path.exists(os.path.join(TOP, path)):
            sys.exit(f"proof-links: no source for {name} ({mod})")
        found[name] = (path, int(start), int(sel), int(end))
    return found


def span(path, start, sel, end, whole):
    """The lines from the docstring through the statement, or the end."""
    lines = open(os.path.join(TOP, path)).read().split("\n")
    a = start
    if a > 1 and lines[a - 2].rstrip().endswith("-/"):  # a docstring the range left out
        while a > 1 and "/--" not in lines[a - 2]:
            a -= 1
        a -= 1
    if whole:
        return a, end
    b = sel
    for i in range(sel - 1, min(sel + 60, len(lines))):
        code = lines[i].split("--")[0]
        if ":=" in code or code.rstrip().endswith(" where"):
            b = i + 1
            break
        if code.lstrip().startswith("|"):
            b = i
            break
    return a, max(b, sel)


def main():
    check = "--check" in sys.argv[1:]
    decls = ranges()
    text = open(README).read()
    if BEGIN not in text:
        text = text.rstrip("\n") + f"\n\n{BEGIN}\n{END}\n"
    head, rest = text.split(BEGIN)
    block_old, tail = rest.split(END)
    problems, labels = [], []
    for label in re.findall(r"\[`([^`\]]+)`\](?![(\[])", head):
        if label not in labels:
            labels.append(label)
    defs = []
    for label in labels:
        hits = [n for n in decls if n == label or n.endswith("." + label)]
        if len(hits) != 1:
            problems.append(f"[`{label}`] names {len(hits)} audited theorems{': ' + ', '.join(hits) if hits else ''}")
            continue
        path, start, sel, end = decls[hits[0]]
        a, b = span(path, start, sel, end, hits[0] in ASSUMED)
        defs.append(f"[`{label}`]: {path}#L{a}-L{b}")
    block = "\n" + "\n".join(defs) + "\n"
    count = re.search(r"All (\d+) rest on", head)
    if not count:
        problems.append('no "All N rest on" count in the README')
    elif int(count.group(1)) != AUDITED[0]:
        if check:
            problems.append(f"the README says All {count.group(1)}; the audit holds {AUDITED[0]}")
        head = head[:count.start(1)] + str(AUDITED[0]) + head[count.end(1):]
    new = head + BEGIN + block + END + tail
    if check:
        if new != text:
            problems.append("the links are stale: run ci/proof-links.py")
        for p in problems:
            print("proof-links:", p)
        print(f"proof-links: {len(defs)} links")
        sys.exit(1 if problems else 0)
    open(README, "w").write(new)
    for p in problems:
        print("proof-links:", p)
    print(f"proof-links: wrote {len(defs)} links")
    sys.exit(1 if problems else 0)


main()
