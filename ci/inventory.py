#!/usr/bin/env python3
"""The cost inventories cannot claim a law that is not proven.

docs/BOUNDS.md and docs/PERF.md list each step of the node's and the
app's loops with its bound and a status: ✅ proven, 🟡 proven of a model
the running code is not yet shown to perform, 📏 bounded by a cap the
code checks and measured, ❌ grows with the store, with its fix. In each
table with a `theorem` column and a status (a `status` column, or the
first mark in a `status and plan` column):

- a ✅ or 🟡 row names at least one theorem in backticks, and every name
  in backticks there is a law the axiom audit lists (tests/Axioms.lean),
  by its full name or a suffix of it;
- a ❌ row says what fixes it ("fix:"), or that it is "as" another row.

  ci/inventory.py [files...]   (default: docs/BOUNDS.md docs/PERF.md)

Its negative control runs first: a table whose ✅ row names a law the
audit lacks, and whose ❌ row has no fix, must fail both ways.
"""
import os, re, sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUDIT = os.path.join(TOP, "tests", "Axioms.lean")
MARKS = ("✅", "🟡", "📏", "❌")


def audited(path=AUDIT):
    names = re.findall(r"^#print axioms (\S+)", open(path).read(), re.M)
    return set(names)


def known(name, laws):
    return any(l == name or l.endswith("." + name) for l in laws)


def cells(line):
    return [c.strip() for c in line.strip().strip("|").split("|")]


def tables(text):
    """Each table as (header cells, [(line number, row cells)])."""
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        if lines[i].startswith("|") and i + 1 < len(lines) and re.match(r"^\|[-| :]+\|$", lines[i + 1]):
            head = [h.lower() for h in cells(lines[i])]
            rows, j = [], i + 2
            while j < len(lines) and lines[j].startswith("|"):
                rows.append((j + 1, cells(lines[j])))
                j += 1
            yield head, rows
            i = j
        else:
            i += 1


def check(path, laws):
    bad = []
    for head, rows in tables(open(path).read()):
        if "theorem" not in head:
            continue
        th = head.index("theorem")
        st = next((k for k, h in enumerate(head) if h.startswith("status")), None)
        if st is None:
            continue
        for n, row in rows:
            if len(row) <= max(th, st):
                continue
            status = row[st]
            mark = next((m for m in sorted(MARKS, key=status.find) if m in status), None)
            names = re.findall(r"`([A-Za-z_][\w.'₀-₉]*)`", row[th])
            where = f"{os.path.relpath(path, TOP)}:{n}"
            if mark in ("✅", "🟡"):
                if not names:
                    bad.append(f"{where}: {mark} names no theorem")
                for x in names:
                    if not known(x, laws):
                        bad.append(f"{where}: {mark} names `{x}`, which the audit does not list")
            if mark == "❌" and "fix" not in " ".join(row).lower() and "❌ as " not in status:
                bad.append(f"{where}: ❌ without a fix")
    return bad


def control(laws):
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as f:
        f.write("| step | bound | theorem | status |\n|---|---|---|---|\n"
                "| a | 1 | `no_such_law_anywhere` | ✅ |\n| b | n | none | ❌ grows |\n")
    try:
        bad = check(f.name, laws)
    finally:
        os.unlink(f.name)
    if len(bad) != 2:
        sys.exit(f"inventory: the negative control was not caught ({bad})")


def main(argv):
    control(audited(os.environ.get("AUDIT", AUDIT)))
    files = argv or [os.path.join(TOP, "docs", f) for f in ("BOUNDS.md", "PERF.md")]
    laws = audited(os.environ.get("AUDIT", AUDIT))
    bad, seen = [], 0
    for f in files:
        if os.path.exists(f):
            seen += 1
            bad += check(f, laws)
    for b in bad:
        print(b)
    print(f"inventory: {seen} files, {len(bad)} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
