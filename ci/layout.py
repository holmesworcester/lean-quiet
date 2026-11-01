#!/usr/bin/env python3
"""The op tree's layout, enforced (docs/OP_WORKSPACE_REQUIREMENTS.md, LAYOUT01-06).

- **Eight names.** Every file under app/ is Op, Validate, View, Commands,
  Screen, Proofs, Tests or Family `.lean` (LAYOUT02).
- **An op is a folder.** A folder with Op.lean has Validate.lean; a folder
  without one groups ops (it has child folders) or is a planned op
  (PLANNED, with what it is today) (LAYOUT01).
- **Registered.** Each family (a folder right under app/) has Family.lean,
  and it imports every Op.lean and Validate.lean below it: the closed sum
  is the registry (LAYOUT02, ARCH01).
- **Downward imports.** A module under app/ imports app/ modules only in
  its own folder's subtree or in an ancestor folder (the ops it cites and
  their registries); a validator also imports the Op.lean of each op it
  cites, typed (ARCH04: the connection family is flat, and established
  cites the reply, the request and the ephemeral key); across the
  families only as CROSS lets: connection ops cite community facts
  (LAYOUT03, ARCH03).
- **A lower engine.** No module under engine/ imports app/ (ARCH03,
  LAYOUT06).

  ci/layout.py               check the tree
  ci/layout.py --self-test   the check on the tree, then on copies of its
                             file list each broken one way: each must fail
"""
import os, re, subprocess, sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NAMES = {"Op", "Validate", "View", "Commands", "Screen", "Proofs", "Tests", "Family"}
# planned ops: a folder that is not yet an op, and what it holds today
PLANNED = {
    "app/community/channel": "the channel op; today its message family's folder",
    "app/community/channel/message/draft": "the draft op; today the composer (View.lean)",
}
# family -> families its modules may import (connection ops cite community facts)
CROSS = {"app/connection": ["app/community"]}
IMPORT = re.compile(r"^import\s+(\S+)", re.M)
# the app's own root modules, beside app/: the engine imports none of them
ROOTS = {"Quiet", "Main"}


def files_of():
    out = subprocess.run(["git", "ls-files", "app", "engine"], cwd=TOP, capture_output=True, text=True, check=True)
    return {f: open(os.path.join(TOP, f), encoding="utf-8").read() for f in out.stdout.split() if f.endswith(".lean")}


def check(src):
    """Problems with a tree given as {path: text}."""
    bad = []
    app = {f for f in src if f.startswith("app/")}
    mod = {f[:-5].replace("/", "."): f for f in src}
    folders = {os.path.dirname(f) for f in app}
    for d in list(folders):
        while d != "app":
            d = os.path.dirname(d)
            folders.add(d)
    for f in sorted(app):
        if os.path.basename(f)[:-5] not in NAMES:
            bad.append(f"{f}: not one of the eight names")
    for d in sorted(folders - {"app"}):
        has = {os.path.basename(f)[:-5] for f in app if os.path.dirname(f) == d}
        kids = [x for x in folders if os.path.dirname(x) == d]
        if "Op" in has and "Validate" not in has:
            bad.append(f"{d}: an op without Validate.lean")
        if "Op" not in has and not kids and d not in PLANNED:
            bad.append(f"{d}: neither an op (Op.lean) nor a family (child folders) nor planned")
    for fam in sorted(x for x in folders if os.path.dirname(x) == "app"):
        reg = f"{fam}/Family.lean"
        if reg not in src:
            bad.append(f"{fam}: a family without Family.lean")
            continue
        imported = set(IMPORT.findall(src[reg]))
        for f in sorted(app):
            if f.startswith(fam + "/") and os.path.basename(f) in ("Op.lean", "Validate.lean") \
                    and os.path.dirname(f) != fam and f[:-5].replace("/", ".") not in imported:
                bad.append(f"{reg}: does not register {f}")
    for f in sorted(src):
        for i in IMPORT.findall(src[f]):
            if f.startswith("engine/") and i in ROOTS:
                bad.append(f"{f}: the engine imports {i}")
                continue
            if i not in mod or not mod[i].startswith("app/"):
                continue
            t = os.path.dirname(mod[i])
            if f.startswith("engine/"):
                bad.append(f"{f}: the engine imports {i}")
                continue
            if not f.startswith("app/"):
                continue
            d = os.path.dirname(f)
            down = t == d or t.startswith(d + "/")
            up = d.startswith(t + "/") or t == "app"
            fam = "/".join(d.split("/")[:2])
            across = any(t == c or t.startswith(c + "/") for c in CROSS.get(fam, []))
            cited = f.endswith("/Validate.lean") and mod[i].endswith("/Op.lean") and \
                (t.startswith(fam + "/") or across)
            if not (down or up or across or cited):
                bad.append(f"{f}: imports {i}, beside it (neither its subtree nor an ancestor)")
    return bad


def main():
    src = files_of()
    bad = check(src)
    for b in bad:
        print("layout:", b)
    if "--self-test" in sys.argv:
        some_op = next(f for f in sorted(src) if f.endswith("/reaction/Op.lean"))
        fam = "app/community/Family.lean"
        sibling = next(f for f in sorted(src) if f.endswith("/profile/View.lean"))
        cases = [
            ("a ninth name", {**src, "app/community/Laws.lean": ""}),
            ("an op without its validator", {k: v for k, v in src.items() if k != some_op.replace("Op", "Validate")}),
            ("a folder that is nothing", {**src, "app/community/stray/View.lean": ""}),
            ("an op its family does not register",
             {**src, fam: src[fam].replace(f"import {some_op[:-5].replace('/', '.')}\n", "")}),
            ("an import beside it", {**src, some_op: f"import {sibling[:-5].replace('/', '.')}\n" + src[some_op]}),
            ("the engine importing the app", {**src, "engine/core/Core.lean": "import app.Screen\n" + src["engine/core/Core.lean"]}),
            ("the engine importing the app's root", {**src, "engine/core/Core.lean": "import Quiet\n" + src["engine/core/Core.lean"]}),
        ]
        for what, tree in cases:
            if check(tree) == bad:
                print(f"layout: negative control not caught: {what}")
                return 1
            print(f"layout: negative control caught: {what}")
    if bad:
        return 1
    print(f"layout: {sum(f.startswith('app/') for f in src)} files under app/, each named and placed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
