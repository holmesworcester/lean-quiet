#!/usr/bin/env python3
"""Every program that starts threads that never end on their own must
leave by IO.Process.exit (Engine.exitAfter): when `main` returns, the Lean
runtime waits for every task, dedicated ones too, so an uncaught exception
or an early return hangs it, unreported (cjk_scroll, close_ingress).

A program is one of the lakefile's lean_exe roots; it starts such threads
if its module mentions one of MARKERS (runners, the store's writer, the
app, the desktop driver, dedicated tasks). Its `def main` must then call
Engine.exitAfter or IO.Process.exit.

    ci/exits.py              check every program
    ci/exits.py --self-test  the check's own negative control"""
import os
import re
import sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MARKERS = re.compile(r"prio := \.dedicated|App\.start|Desktop\.start|Sim\.new|\.run\.write|"
                     r"\.run\.counters|Tcp\.|Reader\.Worker|StopFlag")
# Programs a fix in flight will convert: each name must still need it.
PENDING: dict = {}


def exits(source):
    m = re.search(r"^(?:unsafe |partial )?def main\b.*", source, re.S | re.M)
    return m is not None and ("Engine.exitAfter" in m.group(0) or "IO.Process.exit" in m.group(0))


def problems(top):
    lake = open(os.path.join(top, "lakefile.lean")).read()
    found = []
    for name, root in re.findall(r"lean_exe (\S+) where\s+root := `(\S+)", lake):
        path = os.path.join(top, root.replace(".", "/") + ".lean")
        if not os.path.exists(path):
            continue
        source = open(path).read()
        if not re.search(r"^(?:unsafe |partial )?def main\b", source, re.M):
            continue
        threads = MARKERS.search(source) is not None
        if name in PENDING:
            if exits(source) or not threads:
                found.append(f"{name}: no longer needs its PENDING entry ({PENDING[name]}); remove it")
            continue
        if threads and not exits(source):
            found.append(f"{name} ({path}): starts threads that never end, but `main` can return; "
                         "wrap it: def main … := Engine.exitAfter …")
    return found


def self_test():
    caught = "def mainBody : IO UInt32 := do\n  let s ← App.start io x db\n  return 0\ndef main : IO UInt32 := mainBody\n"
    fixed = caught.replace("def main : IO UInt32 := mainBody", "def main : IO UInt32 := Engine.exitAfter mainBody")
    assert MARKERS.search(caught) and not exits(caught), "a returning main with threads must be caught"
    assert exits(fixed), "Engine.exitAfter must count as exiting"
    print("exits: self-test passed")


if sys.argv[1:] == ["--self-test"]:
    self_test()
    sys.exit(0)
found = problems(TOP)
for p in found:
    print("exits: " + p)
if found:
    sys.exit(1)
print("exits: every program that starts threads leaves by IO.Process.exit")
