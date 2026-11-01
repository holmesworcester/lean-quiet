#!/usr/bin/env python3
"""docs/HEADLINE.md's surface section, from tests/Headline.lean's output.

tests/Headline.lean runs `#headline` (tests/SpecSurface.lean) over the
proposed headline laws: each law's file and line, its axioms, and its
spec surface split into the app's part, the spec-only part, the assumed
part and bridged mirrors. This writes those numbers and lists between
the surface markers of docs/HEADLINE.md, so that the document never
states a stale count. The prose above the markers is written by hand.

  ci/headline.py [OUT]           rewrite the section, and the appendix
                                 docs/HEADLINE-SURFACES.md (OUT: the output of
                                 `lake env lean tests/Headline.lean`;
                                 without it, run that command)
  ci/headline.py --check [OUT]   fail if the section is stale

Needs the tree built (tests/headline.sh builds it).
"""
import os
import re
import subprocess
import sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOC = os.path.join(TOP, "docs", "HEADLINE.md")
SURFACES = os.path.join(TOP, "docs", "HEADLINE-SURFACES.md")
APPENDIX = """# Headline laws: the app's part of each surface

Written by ci/headline.py from tests/Headline.lean's output; do not
edit. For each recommended law of [HEADLINE.md](HEADLINE.md), the
definitions of its spec surface that are the app's own code: what the
law is about, which runs in the app. The spec-only and assumed parts,
which a reviewer must read, are in HEADLINE.md.
"""
BEGIN = "<!-- surface:begin: written by ci/headline.py; do not edit -->"
END = "<!-- surface:end -->"
# The three groups of tests/Headline.lean, in its order: a group ends at
# its union report ("headline all N laws"), the last at the end.
GROUPS = ["Recommended", "Also considered", "For contrast: a World law"]


def parse(text):
    """The laws' reports and the unions, in order, as dicts."""
    blocks, cur = [], None
    for line in text.splitlines():
        m = re.match(r"^headline (\S+)(?: (\d+) laws)?$", line)
        if m:
            cur = {"name": m.group(1), "union": m.group(1) == "all"}
            blocks.append(cur)
            continue
        m = re.match(r"^  at (\S+)$", line) or re.match(r"^  ([a-z ,-]+?): ?(.*)$", line)
        if cur is not None and m:
            if m.re.pattern.startswith("^  at"):
                cur["at"] = m.group(1)
            else:
                cur[m.group(1)] = m.group(2)
    return blocks


def kinds(s):
    """'predicates (2): A, B; definitions (1): C' as [(label, [names])]."""
    out = []
    for part in filter(None, (p.strip() for p in s.split("; "))):
        m = re.match(r"^(\w+) \((\d+)\): (.*)$", part)
        if m:
            out.append((m.group(1), [n.strip() for n in m.group(3).split(",")]))
    return out


def names(s):
    return [n.strip() for n in s.split(",") if n.strip()]


def code(ns):
    return ", ".join(f"`{n}`" for n in ns) if ns else "none"


def render(blocks):
    """The section, and the appendix: the app's part of each recommended
    law's surface, listed whole."""
    out = []
    appendix = [APPENDIX]
    groups, group = [], []
    for b in blocks:
        if b["union"]:
            groups.append((group, b))
            group = []
        else:
            group.append(b)
    if group:
        groups.append((group, None))
    if len(groups) != len(GROUPS):
        raise SystemExit(f"expected {len(GROUPS)} groups of laws, got {len(groups)}")
    for title, (laws, union) in zip(GROUPS, groups):
        out += [f"### {title}", "",
                "| Law | Where | Axioms | Surface | Of the app | Spec-only | Assumed | Bridged |",
                "|---|---|---|---:|---:|---:|---:|---:|"]
        for b in laws:
            path, line = b["at"].rsplit(":", 1)
            short = b["name"].split(".")[-1]
            ax = b["axioms"].replace(" (standard)", "")
            review = re.match(r"(\d+) of the app, (\d+) spec-only, (\d+) assumed, (\d+) bridged", b["review"])
            app, spec, assumed, bridged = review.groups()
            total = b["surface"].split()[0]
            out.append(f"| [`{short}`](#{anchor(b['name'])}) | [{path}:{line}](../{path}#L{line}) | {ax} "
                       f"| {total} | {app} | {spec} | {assumed} | {bridged} |")
        out.append("")
        if union:
            spec = kinds(union["spec-only, together"].split(": ", 1)[1])
            n = union["spec-only, together"].split(":", 1)[0]
            assumed = union["assumed, together"].split(": ", 1)
            out.append(f"**Together** these laws name {n} spec-only definitions, and "
                       f"{assumed[0]} names of the assumptions they take.")
            out.append("")
            out.append("<details><summary>The spec-only definitions, together</summary>")
            out.append("")
            for label, ns in spec:
                out.append(f"- {label}: {code(ns)}")
            out.append(f"- assumed: {code(names(assumed[1]) if len(assumed) > 1 else [])}")
            out += ["", "</details>", ""]
        for b in laws:
            out.append(f"#### {b['name']}")
            out.append("")
            out.append(f"Named in the statement: {code(names(b['named']))}.")
            out.append("")
            spec = kinds(b["spec-only"])
            out.append("Spec-only, to review: " +
                       ("; ".join(f"{label}: {code(ns)}" for label, ns in spec) if spec else "none") + ".")
            out.append("")
            out.append(f"Assumed: {code(names(b['assumed']))}. Bridged: {fmt_bridged(b['bridged'])}.")
            out.append("")
            if title == GROUPS[0]:
                app = names(b["of the app"])
                appendix += [f"## {b['name']}", "",
                             f"<details><summary>Of the app: {len(app)} definitions</summary>", "",
                             code(app), "", "</details>", ""]
    return "\n".join(out).rstrip("\n") + "\n", "\n".join(appendix).rstrip("\n") + "\n"


def fmt_bridged(s):
    """'M (L1, L2), N (L3)' as '`M` (by `L1`, `L2`), `N` (by `L3`)'."""
    items = re.findall(r"(\S+) \(([^)]*)\)", s)
    return ", ".join(f"`{m}` (by {code(names(ls))})" for m, ls in items) if items else "none"


def anchor(name):
    """GitHub's anchor for a `#### name` heading."""
    return re.sub(r"[^a-z0-9_ -]", "", name.lower()).replace(" ", "-")


def main(argv):
    check = "--check" in argv
    files = [a for a in argv if a != "--check"]
    if files:
        text = open(files[0], encoding="utf-8").read()
    else:
        run = subprocess.run(["lake", "env", "lean", "tests/Headline.lean"], cwd=TOP,
                             capture_output=True, text=True)
        if run.returncode != 0:
            sys.stderr.write(run.stdout + run.stderr)
            return 1
        text = run.stdout
    section, appendix = render(parse(text))
    doc = open(DOC, encoding="utf-8").read()
    if BEGIN not in doc or END not in doc:
        raise SystemExit(f"{DOC}: no surface markers")
    head, rest = doc.split(BEGIN, 1)
    _, tail = rest.split(END, 1)
    new = head + BEGIN + "\n\n" + section + "\n" + END + tail
    old = open(SURFACES, encoding="utf-8").read() if os.path.exists(SURFACES) else ""
    if check:
        if new != doc or appendix != old:
            print("docs/HEADLINE.md's surface section or docs/HEADLINE-SURFACES.md is stale: "
                  "run ci/headline.py", file=sys.stderr)
            return 1
        return 0
    with open(DOC, "w", encoding="utf-8") as f:
        f.write(new)
    with open(SURFACES, "w", encoding="utf-8") as f:
        f.write(appendix)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
