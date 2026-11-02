#!/usr/bin/env python3
"""The standing rules' premise tables, and the README's ✅/🟡 from them.

Every law the README's proof tables cite gets a premise table: each
hypothesis it states (tests/Premises.lean), and what it is stated over
(tests/Wiring.lean's assumptions: the store model, a World's network).
Each premise is tagged:

  [discharged]  the law's vacuity evidence proves it of the running code
                on real data (tests/vacuity/*-report.json)
  [crypto] [env] [base] [trusted]
                an assumption of tests/assumptions.txt with that tag
                ([base]: the trusted base, stated once, allowed under ✅)
  [model]       it names code that does not run (tests/Wiring.lean
                classifies the law a model, naming what it misses)
  [spec]        the law is a lemma about a specification or an assumption
                (an empty subject): it claims nothing of running code

A row may be ✅ only if every law it cites is about running code (or runs
the node's code over a World, or is a lemma about a specification), every
premise of each is [discharged], [env] or [crypto], and the row names each
[crypto] assumption it rests on (its `say`). Otherwise the premises force
it 🟡, and its words must say what it assumes or what is missing. A row
whose premises allow ✅ may still be 🟡 for what its laws do not cover; it
says so (ci/proof-links.py checks). Every assumption has a tag and two sides (rule 2): `sat`,
the real system satisfies it, and `neg`, a degenerate model fails it.
The sides missing today are tests/assumptions-baseline.txt, which may
only shrink.

  ci/premises.py           write docs/PREMISES.md and the rows' ✅/🟡
  ci/premises.py --check   fail if either is stale, a cited law's premise
                           is untagged, a row does not name an assumption
                           it rests on, an assumption is untagged or lacks
                           a side outside the baseline; negative controls
                           first
  ci/premises.py --prune   drop the baseline's lines that are no longer missing
  ci/premises.py --stats   how many rows each tag of the store model gives

Needs the tree built (tests/check.sh builds it).
"""
import importlib.util, os, re, subprocess, sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
README = os.path.join(TOP, "README.md")
REGISTRY = os.path.join(TOP, "tests", "assumptions.txt")
BASELINE = os.path.join(TOP, "tests", "assumptions-baseline.txt")
OUT = os.path.join(TOP, "docs", "PREMISES.md")
OK = {"discharged", "env", "crypto", "base", "holds", "spec"}
UNTAGGED = os.path.join(TOP, "tests", "premises-baseline.txt")
# a 🟡 row's own words for what is missing (as ci/proof-links.py's)
WANTED = re.compile(r"Wanted|Not yet|not proven|Not covered|todo", re.I)
WORST = ["trusted", "model", "crypto", "env", "base", "holds", "spec", "discharged"]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, os.path.join(TOP, path))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def classify():
    """tests/Wiring.lean's output lines, split, and its problems."""
    r = subprocess.run(["lake", "env", "lean", "--run", "tests/Wiring.lean"], cwd=TOP,
                       capture_output=True, text=True)
    rows = [l.split("\t") for l in r.stdout.splitlines() if l.split("\t")[0] in ("law", "assume")]
    problems = [l for l in r.stderr.splitlines() if l.startswith("wiring:")]
    if r.returncode != 0 and not problems:
        problems = [f"tests/Wiring.lean failed (is the tree built, and Main?)\n{r.stdout[-2000:]}{r.stderr[-2000:]}"]
    return rows, problems


def resolver(decls):
    """A reference's law or assumption, if it names one alone (as ci/proof-links.py)."""
    def resolve(label):
        hits = [n for n in decls if n == label or n.endswith("." + label)]
        return hits[0] if len(hits) == 1 else None
    return resolve


def registry(path=REGISTRY):
    """NAME -> {tag, sat, neg, say}."""
    reg = {}
    for line in open(path, encoding="utf-8"):
        if not line.strip() or line.startswith("#"):
            continue
        head, _, say = line.rstrip("\n").partition(" say=")
        name, tag, *rest = head.split()
        f = dict(x.split("=", 1) for x in rest)
        f["say"] = say.strip() or "-"
        reg[name] = {"tag": tag, "sat": f.get("sat", "-"), "neg": f.get("neg", "-"), "say": f.get("say", "-")}
    return reg


def premises():
    """law -> [(binder, statement, constants)], from tests/Premises.lean."""
    r = subprocess.run(["lake", "env", "lean", "--run", "tests/Premises.lean"], cwd=TOP,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"tests/Premises.lean failed (is the tree built?)\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    out = {}
    for line in r.stdout.splitlines():
        p = line.split("\t")
        if p[0] == "law":
            out.setdefault(p[1], [])
        elif p[0] == "premise":
            out.setdefault(p[1], []).append((p[2], p[3], [c for c in p[4].split(",") if c]))
    return out


class Model:
    def __init__(self, reg, rows, prem, evidence):
        self.reg, self.prem, self.evidence = reg, prem, evidence
        self.alias = {}
        self.laws = {}
        for r in rows:
            if r[0] == "assume" and r[2].startswith("="):
                self.alias[r[1]] = r[2][1:].strip()
            elif r[0] == "law":
                # law name class subject missing assumes module premises
                self.laws[r[1]] = {"cls": r[2], "missing": [x for x in r[4].split(", ") if x],
                                   "assumes": [x for x in r[5].split(", ") if x],
                                   "pmodels": [x for x in (r[7] if len(r) > 7 else "").split(", ") if x]}

    def root(self, n):
        seen = set()
        while n in self.alias and n not in seen:
            seen.add(n)
            n = self.alias[n]
        return n

    def assumption(self, c):
        n = self.root(c)
        return n if n in self.reg else None

    def table(self, law):
        """The law's premises: (binder, statement, tag, assumptions)."""
        info = self.laws.get(law, {"cls": "model", "missing": [], "assumes": [], "pmodels": []})
        rows, covered = [], set()
        for b, stmt, consts in self.prem.get(law, []):
            names = sorted({a for a in (self.assumption(c) for c in consts) if a})
            models = [c for c in consts if c in info["missing"] or c in info["pmodels"]]
            if names:
                tag = min((self.reg[a]["tag"] for a in names), key=WORST.index)
                covered |= set(names)
            elif models:
                tag = "model"
            elif law in self.evidence:
                tag = "discharged"
            else:
                tag = None
            rows.append((b, stmt, tag, names))
        for a in sorted({x for x in (self.assumption(c) for c in info["assumes"]) if x} - covered):
            rows.append(("(stated over)", self.root(a), self.reg[a]["tag"], [a]))
        if info["cls"] == "model" and not any(t == "model" for _, _, t, _ in rows):
            if info["missing"]:
                rows.append(("(about)", "code that does not run: " + ", ".join(info["missing"]), "model", []))
            else:
                # an empty subject: a lemma about a specification or an
                # assumption, which claims nothing of running code
                rows.append(("(about)", "a specification or an assumption only", "spec", []))
        if info["cls"] == "world":
            rows.append(("(over a World)", "the network is a model of TCP's: per-session FIFO, loss as a close", "env", []))
        return rows


def proof_rows(text):
    """(line index, cells) of the README's proofs rows."""
    lines = text.split("\n")
    out, inp = [], False
    for i, line in enumerate(lines):
        if line.startswith("#"):
            inp = line.strip() in {"### Security proofs", "### Quality proofs"}
        if not inp or not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) >= 4 and cells[0] in ("✅", "🟡"):
            out.append((i, cells))
    return out


def judge(m, text, resolve, untagged=frozenset()):
    """Per row: its title, its cited laws, the computed status, the problems.
    A row is ✅ when its premises allow it and its own words name nothing
    missing; a law in the untagged baseline may have untagged premises
    (they still make the row 🟡)."""
    results = []
    for i, cells in proof_rows(text):
        title = re.sub(r"\*\*(.+?)\*\*.*", r"\1", cells[2]).strip()
        labels = re.findall(r"\[`([^`\]]+)`\](?![(\[])", cells[3])
        laws = [(l, resolve(l)) for l in labels]
        problems, rests, must, ok = [], set(), set(), True
        for label, law in laws:
            if not law:
                problems.append(f'"{title}": [`{label}`] names no audited law')
                ok = False
                continue
            if m.laws.get(law, {}).get("cls") == "control":
                continue
            for b, stmt, tag, names in m.table(law):
                if tag is None:
                    if law not in untagged:
                        problems.append(f'"{title}": {law}: premise {b} ({stmt[:80]}) is untagged: give the law vacuity evidence, or name its assumption in tests/assumptions.txt')
                    ok = False
                elif tag not in OK:
                    ok = False
                if tag in ("crypto", "env", "trusted", "base"):
                    rests |= set(names)
                if tag in ("crypto", "trusted"):
                    must |= set(names)
                if tag == "env" and b == "(over a World)":
                    rests.add("(a World's network)")
        for a in sorted(must):
            say = m.reg[a]["say"]
            short = a.split(".")[-1]
            if say != "-" and not re.search(say, cells[2], re.I) and f"`{short}`" not in cells[2]:
                problems.append(f'"{title}" rests on {a} but does not say so (its `say`: {say})')
        # premises that are not discharged, env or crypto force 🟡; with
        # them all allowed, a row may still be 🟡 for what its laws do not
        # cover, which its own words must say (ci/proof-links.py checks)
        status = "🟡" if not ok else cells[0]
        if status == "🟡" and not WANTED.search(cells[2]) and ok is False:
            # the premises make it 🟡; its words must say so
            if not re.search(r"assum", cells[2], re.I):
                problems.append(f'"{title}" rests on an untrusted premise but its words say neither what is missing nor what it assumes')
        results.append({"line": i, "cells": cells, "title": title, "laws": laws,
                        "status": status, "problems": problems, "rests": sorted(rests)})
    return results


def sides(reg, baseline):
    """Assumptions lacking a side, outside the baseline; and baseline lines now present."""
    bad, missing = [], set()
    for name, e in reg.items():
        if e["tag"] == "holds":
            continue
        for side in ("sat", "neg"):
            w = e[side]
            present = w != "-" and witness_exists(w, theorem=(side == "neg"))
            if not present:
                missing.add(f"{name} {side}")
                if f"{name} {side}" not in baseline:
                    bad.append(f"{name}: no {side} ({'the real system satisfies it' if side == 'sat' else 'a degenerate model fails it'}): " +
                               ("name one in tests/assumptions.txt" if w == "-" else f"{w} is not found"))
    return bad, missing


def witness_exists(w, theorem=False):
    """A tests/vacuity declaration, by name (Vacuity.File.decl); a negation for `neg`."""
    parts = w.split(".")
    if len(parts) < 3 or parts[0] != "Vacuity":
        return False
    path = os.path.join(TOP, "tests", "vacuity", parts[1] + ".lean")
    if not os.path.exists(path):
        return False
    src = open(path, encoding="utf-8").read()
    kind = r"theorem" if theorem else r"(?:theorem|def)"
    mt = re.search(rf"^{kind} {re.escape(parts[-1])}\b(.*?)(?::=|:= by)", src, re.M | re.S)
    if not mt:
        return False
    return (not theorem) or "¬" in mt.group(1)


def write_tables(m, results):
    out = ["# Premise tables", "",
           "Generated by ci/premises.py from tests/Premises.lean, tests/Wiring.lean,",
           "tests/assumptions.txt and the vacuity evidence; do not edit. Each README",
           "proofs row, then each law it cites with every premise and its tag:",
           "[discharged] (vacuity evidence proves it of the running code on real",
           "data), [crypto], [env], [trusted] (tests/assumptions.txt), [model] (names",
           "code that does not run). A row may be ✅ only if every premise is",
           "[discharged], [env] or [crypto], and it names each assumption.", ""]
    for r in results:
        out.append(f"## {r['status']} {r['title']}")
        if r["rests"]:
            out.append("")
            out.append("Rests on: " + ", ".join(f"`{a}`" for a in r["rests"]))
        for label, law in r["laws"]:
            if not law:
                continue
            cls = m.laws.get(law, {}).get("cls", "?")
            out += ["", f"**`{law}`** ({cls})", "", "| premise | statement | tag |", "|---|---|---|"]
            t = m.table(law)
            if not t:
                out.append("| (none) | | |")
            for b, stmt, tag, _ in t:
                s = stmt.replace("|", "\\|")
                if len(s) > 160:
                    s = s[:157] + "…"
                out.append(f"| {b} | `{s}` | [{tag or 'untagged'}] |")
        out.append("")
    return "\n".join(out) + "\n"


def main():
    args = sys.argv[1:]
    vac = load("vacuity", "ci/vacuity.py")
    reg = registry()
    rows, problems = classify()
    if problems:
        raise SystemExit("\n".join(problems))
    evidence = {e["theorem"] for e in vac.CHECKS.values()}
    m = Model(reg, rows, premises(), evidence)
    names = sorted(m.laws) + sorted(m.alias) + sorted(reg)
    resolve = resolver(names)
    text = open(README, encoding="utf-8").read()
    baseline = set()
    if os.path.exists(BASELINE):
        baseline = {l.strip() for l in open(BASELINE) if l.strip() and not l.startswith("#")}
    bad = []
    # every assumption is in the registry, tagged
    for r in rows:
        if r[0] == "assume" and not r[2].startswith("=") and r[1] not in reg:
            bad.append(f"{r[1]}: an assumption with no tag: add it to tests/assumptions.txt")
    side_bad, missing = sides(reg, baseline)
    bad += side_bad
    if "--prune" in args:
        res = judge(m, open(README, encoding="utf-8").read(), resolver(sorted(m.laws) + sorted(m.alias) + sorted(reg)))
        still = {law for r in res for _, law in r["laws"] if law and any(t is None for _, _, t, _ in m.table(law))}
        old_u = {l.split()[1] for l in open(UNTAGGED) if l.startswith("law ")} if os.path.exists(UNTAGGED) else set()
        open(UNTAGGED, "w").write("# Cited laws whose premises are untagged today (no vacuity evidence); may only shrink.\n" +
                                  "".join(f"law {l}\n" for l in sorted(old_u & still)))
        keep = [l for l in sorted(baseline) if l in missing]
        open(BASELINE, "w").write("# Assumption sides missing today (ci/premises.py); this list may only shrink.\n" +
                                  "".join(k + "\n" for k in keep))
        print(f"premises: baseline {len(baseline)} -> {len(keep)}")
        return
    untagged = set()
    if os.path.exists(UNTAGGED):
        untagged = {l.split()[1] for l in open(UNTAGGED) if l.startswith("law ")}
    stale_base = sorted(baseline - missing)
    if stale_base and "--check" in args:
        bad.append("tests/assumptions-baseline.txt lists sides now present (run ci/premises.py --prune): " + ", ".join(stale_base))
    if "--stats" in args:
        for tag in ("trusted", "env"):
            reg2 = {k: dict(v) for k, v in reg.items()}
            reg2["Engine.Model.run"]["tag"] = tag
            m2 = Model(reg2, rows, m.prem, evidence)
            res = judge(m2, text, resolve)
            print(f"store model [{tag}]: {sum(r['status'] == '✅' for r in res)} ✅, {sum(r['status'] == '🟡' for r in res)} 🟡 of {len(res)} rows")
        return
    if "--check" in args:
        # negative controls first: each broken input must be caught
        caught = []
        reg2 = {k: dict(v) for k, v in reg.items()}
        reg2["Trust.NativeCrypto"]["tag"] = "trusted"
        r2 = judge(Model(reg2, rows, m.prem, evidence), text, resolve, frozenset(untagged))
        caught.append(any(r["title"].startswith("Both ends hold one session") and r["status"] == "🟡" for r in r2))
        law0 = resolve("established_agrees_sodium")
        r3 = judge(Model(reg, rows, m.prem, evidence - {law0}), text, resolve, frozenset(untagged))
        caught.append(any("untagged" in p and law0 in p for r in r3 for p in r["problems"]))
        reg4 = {k: dict(v) for k, v in reg.items()}
        reg4["Trust.NativeCrypto"]["neg"] = "-"
        caught.append(any("Trust.NativeCrypto: no neg" in b for b in sides(reg4, baseline)[0]))
        if not all(caught):
            bad.append(f"negative controls escaped (a [trusted] premise under ✅, an untagged premise, a missing side): {caught}")
        else:
            print("premises: negative controls: a [trusted] premise under ✅, an unwitnessed law and a missing side, all caught")
    results = judge(m, text, resolve, frozenset(untagged))
    still = {law for r in results for _, law in r["laws"] if law and any(t is None for _, _, t, _ in m.table(law))}
    if "--check" in args and untagged - still:
        bad.append("tests/premises-baseline.txt lists laws now fully tagged (run ci/premises.py --prune): " + ", ".join(sorted(untagged - still)))
    for r in results:
        bad += r["problems"]
    lines = text.split("\n")
    flips = []
    for r in results:
        if r["cells"][0] != r["status"]:
            flips.append(f'{r["cells"][0]} -> {r["status"]} "{r["title"]}"')
            ln = lines[r["line"]]
            lines[r["line"]] = ln.replace(f"| {r['cells'][0]} |", f"| {r['status']} |", 1)
    new_text = "\n".join(lines)
    tables = write_tables(m, results)
    old_tables = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
    if "--check" in args:
        if flips:
            bad.append("rows whose ✅/🟡 the premises do not give (run ci/premises.py): " + "; ".join(flips))
        if tables != old_tables:
            bad.append("docs/PREMISES.md is stale (run ci/premises.py)")
        if bad:
            raise SystemExit("premises:\n  " + "\n  ".join(bad))
        print(f"premises: {len(results)} rows agree with their premise tables; "
              f"{sum(len(m.table(l)) for r in results for _, l in r['laws'] if l)} premises tagged")
        return
    open(README, "w", encoding="utf-8").write(new_text)
    open(OUT, "w", encoding="utf-8").write(tables)
    for f in flips:
        print("premises: " + f)
    for b in bad:
        print("premises: " + b)
    print(f"premises: wrote docs/PREMISES.md ({len(results)} rows)")


if __name__ == "__main__":
    main()
