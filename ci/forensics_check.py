#!/usr/bin/env python3
"""The forensics tool's deterministic findings, gated (ci/forensics.sh).

Always fails on: a declaration resting on sorry, native_decide or an axiom
beyond Lean's three (propext, Quot.sound, Classical.choice); a kernel
escape hatch in the source (debug.skipKernelTC, #exit).

Fails on a statement smell not in ci/forensics-baseline.txt, which lists
today's and may only shrink:
  reflexiveConclusion, trivialConclusion, conclusionUnfoldsToTrue  a law
      that says nothing (a degenerate witness: `x = x` after instantiation)
  falseHypothesis, contradictoryHypotheses  a vacuous law
  trivialPredicate, emptyPredicate  a Prop that is constantly True/False
  unusedHypothesis  a premise the law does not need

  ci/forensics_check.py MODEL            check
  ci/forensics_check.py MODEL --prune    drop baseline lines no longer found
  ci/forensics_check.py MODEL --seed     write today's findings as the baseline
"""
import json, os, re, sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(TOP, "ci", "forensics-baseline.txt")
STANDARD = {"propext", "Quot.sound", "Classical.choice"}
SMELLS = {"reflexiveConclusion", "trivialConclusion", "conclusionUnfoldsToTrue", "falseHypothesis",
          "contradictoryHypotheses", "trivialPredicate", "emptyPredicate", "unusedHypothesis"}
HATCHES = {"debug.skipKernelTC", "#exit"}


def smell_kind(s):
    return (s.get("code") or s.get("kind") or s.get("type")) if isinstance(s, dict) else str(s)


def smell_what(s):
    """The hypothesis or variable a smell names, if any (its message's first `x`)."""
    m = re.search(r"`([^`]+)`", s.get("msg", "")) if isinstance(s, dict) else None
    return m.group(1) if m else ""


def main():
    path = sys.argv[1]
    m = json.load(open(path))
    always, found = [], set()
    for d in m["decls"]:
        name = d.get("name", "?")
        for a in d.get("axioms", []):
            if a not in STANDARD:
                always.append(f"{name} rests on {a}")
        for s in d.get("smells", []):
            k = smell_kind(s)
            if k in SMELLS:
                found.add(f"{k}\t{name}\t{smell_what(s)}".rstrip("\t"))
    for s in m.get("suppressions", []):
        what = f'{s.get("kind", "")} {s.get("text", "")}'
        if any(h in what for h in HATCHES) or s.get("kind") in ("skipKernelTC", "exit"):
            always.append(f"escape hatch: {what} at {s.get('file')}:{s.get('line')}")
    base = set()
    if os.path.exists(BASELINE):
        base = {l.rstrip("\n") for l in open(BASELINE) if l.strip() and not l.startswith("#")}
    header = "# Forensics statement smells allowed today (ci/forensics_check.py); may only shrink.\n"
    if "--seed" in sys.argv:
        open(BASELINE, "w").write(header + "".join(f + "\n" for f in sorted(found)))
        print(f"forensics: seeded {len(found)} findings")
        return
    if "--prune" in sys.argv:
        keep = sorted(base & found)
        open(BASELINE, "w").write(header + "".join(f + "\n" for f in keep))
        print(f"forensics: baseline {len(base)} -> {len(keep)}")
        return
    new = sorted(found - base)
    gone = sorted(base - found)
    bad = always + [f"new smell: {f}" for f in new]
    if gone:
        bad.append("ci/forensics-baseline.txt lists findings now gone (run with --prune): " + "; ".join(gone))
    if bad:
        raise SystemExit("forensics:\n  " + "\n  ".join(bad))
    print(f"forensics: {len(m['decls'])} declarations, standard axioms only, no escape hatch; "
          f"{len(found)} known smells (baseline), none new")


if __name__ == "__main__":
    main()
