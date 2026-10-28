#!/usr/bin/env python3
"""Rewrites `import` lines from the old module names to the new ones.

The old names are those of f1bfd62's five Lake packages (engine, app, qr,
mdns, net); the new ones are paths from the repository's root
(docs/LAYOUT.md). ci/reorg-map.tsv pairs them, one line per moved file.
For a branch begun on the old layout: merge, move each of its new Lean
files into the new tree, then run this on them.

  ci/reorg-imports.py FILE...            rewrite the files in place
  ci/reorg-imports.py --check FILE...    only say what would change; exit 1 if anything would
  ci/reorg-imports.py --part qr FILE...  read the files as the qr package's
  ci/reorg-imports.py --self-test        rewrite a copy of every Lean file of
                                         f1bfd62; its imports must be those of
                                         the file's new path in the commit that
                                         added the map

Only `import` lines change. A name that is already new, or that no old
package had (Std, Lean), is left alone. One old name, `Tests.Check`, was
both qr's and mdns's: a file is read as one package's by --part, else by
its path (under `qr/`, or a new path the map gives one of qr's files);
otherwise that import is reported and left as it is. The app imported
the engine's and qr's modules, and net the engine's, so their names
resolve across packages.
"""
import os, re, subprocess, sys, tempfile

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAP = os.path.join(TOP, "ci", "reorg-map.tsv")
PARTS = ["engine", "app", "qr", "mdns", "net"]
OLD = "f1bfd62"
# what each old package required
DEPS = {"engine": [], "app": ["engine", "qr"], "qr": [], "mdns": [], "net": ["engine"]}
IMPORT = re.compile(r"^(\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)([\w.'«»]+)(.*)$")


def load():
    olds, part_of = {}, {}
    for line in open(MAP, encoding="utf-8"):
        if line.startswith("#") or line.startswith("old_path\t"):
            continue
        old_path, new_path, old_mod, new_mod = line.rstrip("\n").split("\t")[:4]
        part = old_path.split("/", 1)[0]
        part_of[old_path] = part_of[new_path] = part
        if old_mod and new_mod:
            olds.setdefault(old_mod, {})[part] = new_mod
    return olds, part_of


def file_part(path, part_of):
    rel = os.path.relpath(os.path.abspath(path), TOP)
    if rel in part_of:
        return part_of[rel]
    first = rel.split(os.sep, 1)[0]
    return first if first in PARTS else None


def resolve(name, part, olds):
    """The new name of old module `name`, read from package `part`."""
    by = olds.get(name)
    if not by:
        return None, None
    if len(by) == 1:
        return next(iter(by.values())), None
    if part:
        for p in [part] + DEPS[part]:
            if p in by:
                return by[p], None
    return None, f"{name} was a module of {' and '.join(sorted(by))}: give --part"


def git(*args):
    return subprocess.run(["git", *args], cwd=TOP, capture_output=True, text=True, check=True).stdout


def imports(text):
    return [l.strip() for l in text.split("\n") if IMPORT.match(l)]


def self_test():
    """Every Lean file of OLD, rewritten, against its new path; then a
    shared old name with and without --part, --check, and a second run."""
    new = git("log", "-1", "--format=%H", "--diff-filter=A", "--", "ci/reorg-map.tsv").strip()
    show = (lambda p: git("show", f"{new}:{p}")) if new else (lambda p: open(os.path.join(TOP, p)).read())
    me = [sys.executable, os.path.abspath(__file__)]
    bad, n = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        for line in open(MAP, encoding="utf-8"):
            row = line.rstrip("\n").split("\t")
            if line.startswith("#") or row[0] == "old_path" or not row[0].endswith(".lean") or row[4]:
                continue
            old_path, new_path = row[0], row[1]
            f = os.path.join(tmp, old_path.replace("/", "_"))
            open(f, "w").write(git("show", f"{OLD}:{old_path}"))
            r = subprocess.run(me + ["--part", old_path.split("/")[0], f], capture_output=True, text=True)
            got, want = imports(open(f).read()), imports(show(new_path))
            n += 1
            if r.returncode != 0 or got != want:
                bad.append(f"{old_path} -> {new_path}: {got} != {want}\n{r.stdout}")
        f = os.path.join(tmp, "Shared.lean")
        text = "import Tests.Check\nimport Std.Data.HashMap\nimport Qr\n\ndef x := 0\n"
        open(f, "w").write(text)
        r = subprocess.run(me + [f], capture_output=True, text=True)
        if r.returncode == 0 or "give --part" not in r.stdout or imports(open(f).read())[0] != "import Tests.Check":
            bad.append(f"a shared old name without --part was not refused: {r.stdout}")
        for part, mod in [("qr", "tests.qr.Check"), ("mdns", "tests.mdns.Check")]:
            open(f, "w").write(text)
            subprocess.run(me + ["--part", part, f], capture_output=True, text=True)
            want = [f"import {mod}", "import Std.Data.HashMap", "import engine.renderer.qr.Qr"]
            if imports(open(f).read()) != want or not open(f).read().endswith("\ndef x := 0\n"):
                bad.append(f"--part {part}: {open(f).read()!r}")
        r = subprocess.run(me + ["--part", "mdns", f], capture_output=True, text=True)
        if r.returncode != 0 or "0 imports rewritten" not in r.stdout:
            bad.append(f"a second run changed something: {r.stdout}")
        open(f, "w").write(text)
        r = subprocess.run(me + ["--check", "--part", "qr", f], capture_output=True, text=True)
        if r.returncode == 0 or open(f).read() != text:
            bad.append(f"--check wrote or passed: {r.stdout}")
    for b in bad:
        print("reorg-imports self-test:", b)
    print(f"reorg-imports self-test: {n} files rewritten, {len(bad)} wrong")
    sys.exit(1 if bad else 0)


def main(argv):
    if argv == ["--self-test"]:
        self_test()
    check = "--check" in argv
    part = None
    files = []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--check":
            pass
        elif a == "--part":
            i += 1
            part = argv[i]
            if part not in PARTS:
                sys.exit(f"reorg-imports: --part is one of {', '.join(PARTS)}")
        elif a.startswith("-"):
            sys.exit(__doc__)
        else:
            files.append(a)
        i += 1
    if not files:
        sys.exit(__doc__)
    olds, part_of = load()
    changed, problems = 0, 0
    for f in files:
        p = part or file_part(f, part_of)
        lines = open(f, encoding="utf-8").read().split("\n")
        out = []
        for n, line in enumerate(lines, 1):
            m = IMPORT.match(line)
            if m:
                new, why = resolve(m.group(2), p, olds)
                if why:
                    print(f"{f}:{n}: {why}")
                    problems += 1
                elif new and new != m.group(2):
                    print(f"{f}:{n}: import {m.group(2)} -> {new}")
                    line = m.group(1) + new + m.group(3)
                    changed += 1
            out.append(line)
        if not check:
            text = "\n".join(out)
            if text != "\n".join(lines):
                open(f, "w", encoding="utf-8").write(text)
    print(f"reorg-imports: {changed} import{'s' if changed != 1 else ''} {'to rewrite' if check else 'rewritten'}"
          + (f", {problems} left ambiguous" if problems else ""))
    sys.exit(1 if problems or (check and changed) else 0)


main(sys.argv[1:])
