#!/usr/bin/env python3
"""The README's theorem links, from Lean's own declaration ranges, and
its list of laws not yet about running code, from tests/Wiring.lean.

Every theorem the audit lists (`#print axioms` in tests/Axioms.lean) is
looked up in the built environment (`findDeclarationRanges?`), and linked
to its file and lines: from its docstring through its statement, not its
proof. The assumptions (tests/wiring.txt's `assume`s) are linked whole,
definition included.

The README names a theorem as a shortcut reference, [`no_impersonation`],
by its full name or any suffix of it that names one of these; the link
definitions go in the block between the proof-links markers at its end.

The section between the wiring markers ("Not yet about running code") is
written from tests/Wiring.lean's classification: how many laws are about
running code, per area; a row for each missing link with its laws and
tests/wiring.txt's note; the statements stated only; the assumptions.
The proofs tables above it must agree: a ✅ row must cite a law about
running code, and a 🟡 row must say what is missing ("Wanted", "Not
yet", "not proven", "Not covered", "todo"), itself or in the section its
More link opens. The
README's lead takes its number from the same count ("N of M are about
the code that runs"), and may say "nearly every" only while that is
90% or more.

  ci/proof-links.py           rewrite the block and the section
  ci/proof-links.py --check   fail if either is stale, a reference
                              names no audited theorem, the README's
                              "All N rest on" count is not the audit's,
                              tests/Wiring.lean fails (a law marked wired
                              is not, a stale note), or a proofs row
                              disagrees. Negative controls first: notes
                              marking a model law wired, a ✅ row citing
                              only it, and a 🟡 row saying nothing missing
                              must each fail.

Needs the tree built (tests/check.sh builds it).
"""
import os, re, subprocess, sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUDIT = os.path.join(TOP, "tests", "Axioms.lean")
README = os.path.join(TOP, "README.md")
NOTES = os.path.join(TOP, "tests", "wiring.txt")
BEGIN = "<!-- proof-links: written by ci/proof-links.py; do not edit -->"
END = "<!-- /proof-links -->"
WBEGIN = "<!-- wiring:begin -->"
WEND = "<!-- wiring:end -->"
# The areas of the per-area counts: the first module prefix a law's
# module has.
AREAS = [("engine.core", "Engine"), ("ops.sync", "Sync"), ("engine.wire.mdns", "mDNS"),
         ("engine.wire", "Node and wire"), ("ops.connection.bootstrap", "Bootstrap"),
         ("ops.connection", "Connections"), ("ops.community", "Community"),
         ("engine.renderer.qr", "QR codes"), ("engine.renderer.pic", "Pictures"),
         ("engine.renderer", "Screen"), ("ops.app", "App"), ("App", "App")]
# What a 🟡 row says to name what is missing.
WANTED = re.compile(r"wanted|not yet|not proven|not covered|todo", re.I)
# The lead's count, and the share "nearly every" needs.
LEAD = re.compile(r"(\d+) of\s+(?:its\s+)?(\d+)\)?\s+(?:theorems\s+)?are\s+about\s+the\s+code\s+that\s+runs")
NEARLY = re.compile(r"(nearly|almost) (every|all) (theorem|law)", re.I)
THRESHOLD = 0.9
# How many theorems the audit lists, counted as they are probed.
AUDITED = [0]


def notes(kind, path=NOTES):
    """tests/wiring.txt's notes of a kind: name to text, in its order."""
    out = {}
    for line in open(path):
        f = line.split(None, 2)
        if len(f) >= 2 and f[0] == kind:
            out[f[1]] = f[2].strip() if len(f) > 2 else ""
    return out


# What the theorems take as hypotheses, and the models they assume.
ASSUMED = list(notes("assume")) + list(notes("holds"))

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


def classify(notes_path=None):
    """tests/Wiring.lean's output: its lines, split, and its problems."""
    env = dict(os.environ, WIRING_NOTES=notes_path) if notes_path else None
    r = subprocess.run(["lake", "env", "lean", "--run", "tests/Wiring.lean"], cwd=TOP,
                       capture_output=True, text=True, env=env)
    rows = [l.split("\t") for l in r.stdout.splitlines()
            if l.split("\t")[0] in ("law", "stmt", "missing", "assume", "copy", "count")]
    problems = [l for l in r.stderr.splitlines() if l.startswith("wiring:")]
    if r.returncode != 0 and not problems:
        problems = [f"tests/Wiring.lean failed (is the tree built, and Main?)\n{r.stdout}{r.stderr}"]
    return rows, problems


def split(cell):
    return [x for x in cell.split(", ") if x]


def short(name, names, least=1):
    """The shortest suffix of name, of `least` parts or more, that names it
    alone among names."""
    parts = name.split(".")
    for k in range(min(least, len(parts)), len(parts) + 1):
        s = ".".join(parts[-k:])
        if sum(1 for n in names if n == s or n.endswith("." + s)) == 1:
            return s
    return name


def resolver(decls):
    """A reference's audited theorem or assumption, if it names one alone."""
    def resolve(label):
        hits = [n for n in decls if n == label or n.endswith("." + label)]
        return hits[0] if len(hits) == 1 else None
    return resolve


def sections(text):
    """Each heading's anchor, with its section's text."""
    out, parts = {}, re.split(r"^(#+ .*)$", text, flags=re.M)
    for h, body in zip(parts[1::2], parts[2::2]):
        anchor = re.sub(r"[^\w\- ]", "", h.lstrip("#").strip().lower()).replace(" ", "-")
        out[anchor] = body
    return out


def disagree(tables, wired, resolve, more={}):
    """The proofs rows that disagree with the classification: a ✅ row that
    cites no law about running code, a 🟡 row that does not say what is
    missing, itself or in the section its More link opens."""
    bad = []
    for line in tables.split("\n"):
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 4 or cells[0] not in ("✅", "🟡"):
            continue
        title = re.sub(r"\*\*(.+?)\*\*.*", r"\1", cells[2]).strip()
        laws = [resolve(l) for l in re.findall(r"\[`([^`\]]+)`\]", cells[3])]
        if cells[0] == "✅" and not any(l in wired for l in laws if l):
            bad.append(f"✅ \"{title}\" cites no law about running code: make it 🟡, saying what is missing")
        opens = [more.get(a, "") for a in re.findall(r"\]\(#([\w-]+)\)", cells[2])]
        if cells[0] == "🟡" and not WANTED.search(cells[2]) and not any(WANTED.search(t) for t in opens):
            bad.append(f"🟡 \"{title}\" does not say what is missing (Wanted, Not yet, not proven, Not covered, todo)")
    return bad


def controls(rows, resolve):
    """The negative controls: notes marking a model law wired, a ✅ row
    citing only it, and a 🟡 row saying nothing missing must each fail."""
    model = next((f[1] for f in rows if f[0] == "law" and f[2] == "model"), None)
    wired = {f[1] for f in rows if f[0] == "law" and f[2] == "wired"}
    if model is None or not wired:
        return []
    problems = []
    os.makedirs(os.path.join(TOP, "out", "proof-links"), exist_ok=True)
    path = os.path.join(TOP, "out", "proof-links", "wiring-control.txt")
    with open(path, "w") as f:
        f.write(open(NOTES).read() + f"\nwired {model}\n")
    _, caught = classify(path)
    if not any(f"marks {model} wired, but it is not" in p for p in caught):
        problems.append(f"negative control: {model}, marked wired, was not caught")
    a_wired = sorted(wired)[0]
    rows_ = (f"| ✅ | 🥊 | **Control.** | [`{model}`] |\n"
             f"| 🟡 | 🥊 | **Control.** Proven. | [`{a_wired}`] |\n")
    if len(disagree(rows_, wired, lambda l: l)) != 2:
        problems.append("negative control: a ✅ row citing only a model law, or a 🟡 row "
                        "saying nothing missing, was not caught")
    if not problems:
        print(f"proof-links: negative controls: {model} marked wired, a ✅ row citing only it, "
              "and a 🟡 row saying nothing missing, all caught")
    return problems


def section(rows, decls, cited):
    """The README's todo section, from tests/Wiring.lean's lines."""
    laws = [(f[1], f[2], split(f[4]), split(f[5]), f[6], split(f[7])) for f in rows if f[0] == "law"]
    stmts = [(f[1], f[2], split(f[4])) for f in rows if f[0] == "stmt"]
    missing = {f[1]: (int(f[2]), f[3], split(f[4])) for f in rows if f[0] == "missing"}
    given = {f[1]: f[2] for f in rows if f[0] == "assume"}
    assumed = {a: given[a] for a in ASSUMED if a in given}  # in tests/wiring.txt's order
    count = dict(c.split(" ") for f in rows if f[0] == "count" for c in f[1:])

    def target(m, table):
        seen = set()
        while m in table and table[m].startswith("= ") and m not in seen:
            seen.add(m)
            m = table[m][2:].strip()
        return m

    notes_of = {m: v[1] for m, v in missing.items()}

    def place(m):
        t = target(m, notes_of)
        return (missing[t][0] if t in missing and missing[t][1] else 10 ** 6, t)

    def link(n, mark="", cite=True):
        """A reference; of two parts when its last is short (`Symbolic.good`)."""
        label = short(n, decls, 1 if len(n.split(".")[-1]) > 4 else 2)
        return f"[`{label}`]" + mark + ("†" if cite and n in cited else "")

    def codes(t, names):
        """A row's definitions, its own first, three at most."""
        ns = [t] + sorted(names - {t}) if t in names else sorted(names)
        more = f" +{len(ns) - 3}" if len(ns) > 3 else ""
        return ", ".join(f"`{short(n, missing, 2)}`" for n in ns[:3]) + more

    # per area
    def area(mod):
        return next((a for p, a in AREAS if mod == p or mod.startswith(p + ".")), "Other")
    per = {}
    for name, status, _, _, mod, _ in laws:
        c = per.setdefault(area(mod), [0, 0])
        c[0 if status == "wired" else 1] += 1
    order = list(dict.fromkeys([a for _, a in AREAS] + ["Other"]))
    out = [f"**{count['wired']} of {len(laws)} laws are about running code.** "
           f"{count['model']} are about a model, a harness, or code nothing calls yet; "
           f"{count['stated']} statements are stated only; {count['assumption']} assumptions.", "",
           "| Area | Laws | About running code | Not yet |", "|---|---|---|---|"]
    for a in order:
        if a in per:
            w, m = per[a]
            out.append(f"| {a} | {w + m} | {w} | {m or ''} |")
    # per missing link
    groups, general, names_model = {}, [], []
    for name, status, miss, _, _, prem in laws:
        if status == "wired":
            if prem:
                names_model.append((name, prem))
            continue
        if not miss:
            general.append(name)
            continue
        only_premise = set(miss) <= set(prem)
        for m in miss:
            t = place(m)[1]
            g = groups.setdefault(t, ({}, set()))
            g[0][name] = only_premise
            g[1].add(m)
    out += ["", "| Missing link | Laws | To make them real |", "|---|---|---|"]
    for t in sorted(groups, key=lambda t: place(t)):
        ls, names = groups[t]
        note = missing[t][1] if t in missing and missing[t][1] else ""
        if not note:
            by = sorted({c for n in names for c in missing.get(n, (0, "", []))[2]} - names)
            note = "Nothing that runs calls it" + (f"; {codes(by[0], set(by))} do" if by else "") + "."
        cell = ", ".join(link(n, "*" if p else "") for n, p in ls.items())
        out.append(f"| {codes(t, names)} | {cell} | {note} |")
    if general:
        out.append(f"| (none) | {', '.join(map(link, general))} | Nothing to wire: each is about "
                   "a specification or an assumption. |")
    out += ["", "\\* only a premise names the model (a reachable state admits the modelled "
            "purge). † a guarantee above cites it."]
    copies = [f for f in rows if f[0] == "copy"]
    if copies:
        out += ["", "**Restates running code** (todo: state it of the real function):", ""]
        out += [f"- {link(f[1]) if f[1] in decls else f'`{short(f[1], missing, 2)}`'} restates "
                f"`{short(f[2], [f[2]], 2)}`: {f[3]}" for f in copies]
    if names_model:
        out += ["", "About running code, but naming a model outside the code they are about: " +
                "; ".join(f"{link(n)} (`{', '.join(short(m, missing, 2) for m in p)}`)"
                          for n, p in names_model) + "."]
    stated = [(n, m) for n, st, m in stmts if st == "stated"]
    out += ["", "**Stated only** (a `…_stmt` no audited law concludes): " +
            ("; ".join(f"`{n}`" + (f" (does not run: {', '.join(f'`{short(x, missing, 2)}`' for x in m)})"
                                   if m else "") for n, m in stated) if stated else "none") + ".", "",
            "**Assumptions,** with the laws that take them or are stated over them:", ""]
    for a, text in assumed.items():
        if text.startswith("= "):
            continue
        part = [a] + [b for b in assumed if b != a and target(b, assumed) == a]
        n = sum(1 for law in laws if set(law[3]) & set(part))
        more = f" +{len(part) - 4}" if len(part) > 4 else ""
        also = f", with {', '.join(f'`{short(b, assumed, 2)}`' for b in part[1:4])}{more}" if part[1:] else ""
        out.append(f"- {link(a, cite=False)}{also} ({n} laws): {text}")
    return "\n" + "\n".join(out) + "\n"


def main():
    check = "--check" in sys.argv[1:]
    decls = ranges()
    resolve = resolver(decls)
    rows, problems = classify()
    if check:
        problems = controls(rows, resolve) + problems
    text = open(README).read()
    if WBEGIN not in text or WEND not in text:
        sys.exit(f"proof-links: no wiring markers ({WBEGIN}, {WEND}) in the README")
    pre, rest = text.split(WBEGIN)
    section_old, post = rest.split(WEND)
    # the proofs tables: "What is proven", above the section
    tables = pre.split("## What is proven")[-1]
    wired = {f[1] for f in rows if f[0] == "law" and f[2] == "wired"}
    total = sum(1 for f in rows if f[0] == "law")
    problems += disagree(tables, wired, resolve, sections(text))
    # the lead's count, and "nearly every" only at the threshold
    lead = LEAD.search(pre)
    if not lead:
        problems.append('no "N of M are about the code that runs" in the README\'s lead')
    elif (int(lead.group(1)), int(lead.group(2))) != (len(wired), total):
        if check:
            problems.append(f"the lead says {lead.group(1)} of {lead.group(2)}; the count is {len(wired)} of {total}")
        pre = pre[:lead.start(1)] + str(len(wired)) + pre[lead.end(1):lead.start(2)] + str(total) + pre[lead.end(2):]
    if total and NEARLY.search(pre) and len(wired) < THRESHOLD * total:
        problems.append(f'the README says "{NEARLY.search(pre).group(0)}", but {len(wired)} of {total} '
                        f"({100 * len(wired) // total}%) is under {int(THRESHOLD * 100)}%")
    cited = {resolve(l) for l in re.findall(r"\[`([^`\]]+)`\]", tables)} - {None}
    section_new = section(rows, decls, cited)
    if check and section_new != section_old:
        problems.append("the wiring section is stale: run ci/proof-links.py")
    text = pre + WBEGIN + section_new + WEND + post
    if BEGIN not in text:
        text = text.rstrip("\n") + f"\n\n{BEGIN}\n{END}\n"
    head, rest = text.split(BEGIN)
    block_old, tail = rest.split(END)
    labels = []
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
        if block != block_old:
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
