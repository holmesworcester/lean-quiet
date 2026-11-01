#!/usr/bin/env python3
"""Interpret Android's component and task diagnostics without counting aliases."""
import re
import sys


def resolves_to(text: str, package: str) -> bool:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if not lines or "/" not in lines[-1]:
        return False
    owner, activity = lines[-1].split("/", 1)
    if activity.startswith("."):
        activity = owner + activity
    return owner == package and activity == package + ".LeanActivity"


def task_ids(text: str, package: str) -> set[int]:
    package_name = re.compile(r"(?<![\w.])" + re.escape(package) + r"(?![\w.])")
    return {
        int(match.group(1))
        for match in re.finditer(r"Task\{[^}\n]*? #(\d+)\b[^}\n]*\}", text)
        if package_name.search(match.group())
    }


def self_test() -> None:
    package = "com.holmes.leanquiet"
    # Captured Android 36 resolve-activity and repeated dumpsys task references.
    short = "priority=0 preferredOrder=0 match=0x308000\ncom.holmes.leanquiet/.LeanActivity\n"
    assert resolves_to(short, package)
    assert resolves_to(package + "/" + package + ".LeanActivity", package)
    assert not resolves_to(package + "/.WrongActivity", package)
    assert not resolves_to("com.other/.LeanActivity", package)
    assert not resolves_to("No activity found", package)
    task = "Task{e84bd63 #6 type=standard A=10216:com.holmes.leanquiet U=0}"
    repeated = "  * " + task + "\nrootOfTask=true task=" + task + "\nfocused=" + task
    assert task_ids(repeated, package) == {6}
    assert task_ids(repeated + "\n" + task.replace("#6", "#7"), package) == {6, 7}
    assert task_ids(task.replace(package, package + "2"), package) == set()
    assert task_ids("Task{abcd #8 type=home}", package) == set()
    print("Android link diagnostics: component aliases and distinct-task controls pass")


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        self_test()
    else:
        mode, package = sys.argv[1:]
        text = sys.stdin.read()
        if mode == "component":
            passed = resolves_to(text, package)
        elif mode == "one-task":
            passed = len(task_ids(text, package)) == 1
        else:
            raise SystemExit("unknown link diagnostic mode")
        raise SystemExit(0 if passed else 1)
