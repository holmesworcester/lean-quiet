#!/usr/bin/env python3
"""Resolve README.md's merge conflicts in what the README's writers write
again after the build, taking main's side (theirs):

- a conflict inside a generated block (wiring, proof-links, vacuity: the
  blocks ci/proof-links.py and ci/vacuity.py write between their markers);
- a conflict outside them whose lines differ only in numbers and the
  lead's fraction word (the counts ci/proof-links.py rewrites).

Any other conflict, a hand-written claim row say, is left for a person:
a branch's new citations would be lost if main's side were taken. Exit 1
when any conflict is left.

The proof tree (docs/PROOF-TREE.md, docs/proof-tree/) is written whole by
ci/proof-tree.py, so each of its conflicts takes main's side.

    ci/readme-merge.py [FILE...]  resolve README.md (or these files) in place
    ci/readme-merge.py --self-test"""
import re
import sys

BEGIN = ("<!-- wiring:begin -->", "<!-- proof-links: written by ci/proof-links.py; do not edit -->",
         "<!-- vacuity:begin -->")
END = ("<!-- wiring:end -->", "<!-- /proof-links -->", "<!-- vacuity:end -->")
WORDS = r"nearly all|nine tenths|four fifths|three quarters|two thirds|three fifths|half"


def shape(line):
    """A line with its numbers and fraction word taken out."""
    return re.sub(WORDS, "F", re.sub(r"\d[\d,]*", "N", line))


def counts_only(ours, theirs):
    return len(ours) == len(theirs) and all(shape(a) == shape(b) for a, b in zip(ours, theirs))


def generated(path):
    """A file written whole by a script: every conflict in it takes main's side."""
    return path == "docs/PROOF-TREE.md" or (path.startswith("docs/proof-tree/") and path.endswith(".md"))


def resolve(text, whole=False):
    """The text with what can be resolved resolved, and the number left;
    `whole`: all of it is generated."""
    lines = text.split("\n")
    out, left, inside, i = [], 0, whole, 0
    while i < len(lines):
        line = lines[i]
        if not line.startswith("<<<<<<< "):
            if line.strip() in BEGIN:
                inside = True
            elif line.strip() in END:
                inside = whole
            out.append(line)
            i += 1
            continue
        start, ours, theirs, part = i, [], [], "ours"
        i += 1
        while not lines[i].startswith(">>>>>>> "):
            if lines[i].startswith("||||||| "):
                part = "base"
            elif lines[i] == "=======":
                part = "theirs"
            elif part == "ours":
                ours.append(lines[i])
            elif part == "theirs":
                theirs.append(lines[i])
            i += 1
        if inside or counts_only(ours, theirs):
            out.extend(theirs)
        else:
            out.extend(lines[start:i + 1])
            left += 1
        i += 1
    return "\n".join(out), left


def conflict(ours, theirs):
    return f"<<<<<<< HEAD\n{ours}\n||||||| base\nbase\n=======\n{theirs}\n>>>>>>> origin/main"


def self_test():
    gen = conflict("| Node and wire | 198 | 132 | 16 | 50 |", "| Node and wire | 201 | 135 | 16 | 50 |")
    lead = conflict("All 1360 rest on Lean's axioms, about two thirds (993 of 1338)",
                    "All 1364 rest on Lean's axioms, about three quarters (995 of 1341)")
    claim = conflict("| 🟡 | x | **A claim.** | [`a`], [`b`] |", "| 🟡 | x | **A claim.** | [`a`] |")
    text, left = resolve(f"{lead}\n<!-- wiring:begin -->\n{gen}\n<!-- wiring:end -->\n")
    assert left == 0 and "201 | 135" in text and "995 of 1341" in text, "generated or counts left"
    text, left = resolve(f"<!-- wiring:begin -->\n{gen}\n<!-- wiring:end -->\n{claim}\n")
    assert left == 1 and "[`a`], [`b`]" in text, "a hand-written row must be left"
    node = conflict("<li>✅ <a href=\"x.lean#L3\">a</a> · 4 below</li>", "<li>✅ <a href=\"x.lean#L5\">a</a></li>")
    text, left = resolve(f"# The proof tree\n{node}\n", whole=generated("docs/proof-tree/sync.md"))
    assert left == 0 and "#L5" in text and "#L3" not in text, "the proof tree takes main's side"
    assert not generated("docs/SYNC.md") and not generated("README.md"), "only the proof tree is whole"
    print("readme-merge: self-test passed")


if sys.argv[1:] == ["--self-test"]:
    self_test()
    sys.exit(0)
left = 0
for path in sys.argv[1:] or ["README.md"]:
    try:
        text = open(path).read()
    except FileNotFoundError:  # deleted on one side: written again after the build
        if generated(path):
            continue
        raise
    text, n = resolve(text, generated(path))
    open(path, "w").write(text)
    left += n
if left:
    print(f"readme-merge: {left} conflict(s) outside the generated lines left to resolve by hand")
sys.exit(1 if left else 0)
