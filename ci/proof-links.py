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
written from tests/Wiring.lean's classification, as short tables: the
count per area; a row for each missing link (a model, or running code a
law restates) with its laws and tests/wiring.txt's note; the
assumptions. The proofs tables above it must agree: a ✅ row must cite a
law about running code, and a 🟡 row must say in its own cell what is
missing ("Wanted", "Not yet", "not proven", "Not covered", "todo"). The
README's lead takes its fraction and number from the same count ("about
three quarters of its theorems (N of M)"): the largest of `FRACTIONS` the
share reaches, so the word never claims more than the number. M leaves
out the negative controls (laws that prove a mutant breaks its law), and
says so when there are any ("N of M, not counting K negative controls");
the World laws are in M, and the lead counts them apart ("another K run
the phone's node code"). It may
say "nearly every" only while the share is 90% or more.

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
AREAS = [("engine.core", "Engine"), ("ops.sync", "Sync"), ("engine.world", "The n-node World"),
         ("engine.wire.mdns", "mDNS"),
         ("engine.wire", "Node and wire"), ("ops.connection.bootstrap", "Bootstrap"),
         ("ops.connection", "Connections"), ("ops.community", "Community"),
         ("engine.renderer.qr", "QR codes"), ("engine.renderer.pic", "Pictures"),
         ("engine.renderer", "Screen"), ("ops.app", "App"), ("App", "App"), ("AppLife", "App"), ("AppTypes", "App")]
# What a 🟡 row says to name what is missing.
WANTED = re.compile(r"wanted|not yet|not proven|not covered|todo", re.I)
# The lead's count, and the share "nearly every" needs.
LEAD = re.compile(r"about\s+([a-z]+(?:\s+[a-z]+)?)\s+of\s+its\s+theorems\s+\((\d+)\s+of\s+(\d+)"
                  r"(,\s+not\s+counting\s+\d+\s+negative\s+controls)?\)")
# The lead's World clause: the laws that run the node's code in a World,
# counted apart from those about running code.
WORLDLEAD = re.compile(r"another\s+(\d+)\s+run\s+the\s+phone's\s+node\s+code")
# The lead's fraction words, each with the share it needs.
FRACTIONS = [(0.95, "nearly all"), (0.9, "nine tenths"), (0.8, "four fifths"), (0.75, "three quarters"),
             (2 / 3, "two thirds"), (0.6, "three fifths"), (0.5, "half")]
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


def disagree(tables, wired, resolve):
    """The proofs rows that disagree with the classification: a ✅ row that
    cites no law about running code, a 🟡 row whose own cell does not say
    what is missing."""
    bad = []
    for line in tables.split("\n"):
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 4 or cells[0] not in ("✅", "🟡"):
            continue
        title = re.sub(r"\*\*(.+?)\*\*.*", r"\1", cells[2]).strip()
        laws = [resolve(l) for l in re.findall(r"\[`([^`\]]+)`\]", cells[3])]
        if cells[0] == "✅" and not any(l in wired for l in laws if l):
            bad.append(f"✅ \"{title}\" cites no law about running code: make it 🟡, saying what is missing")
        if cells[0] == "🟡" and not WANTED.search(cells[2]):
            bad.append(f"🟡 \"{title}\" does not say what is missing (Wanted, Not yet, not proven, Not covered, todo)")
    return bad


def fraction(w, t):
    """The largest fraction word the share w of t reaches."""
    return next((word for f, word in FRACTIONS if w >= f * t), "less than half")


def lead(pre, w, t, k=None, c=0):
    """The lead's problems against the count w of t (and k World laws), and
    the lead written from it. Negative controls (c) are out of t, and the
    lead says so."""
    m = LEAD.search(pre)
    if not m:
        return ['no "about <fraction> of its theorems (N of M)" in the README\'s lead'], pre
    problems = []
    if k is not None:
        x = WORLDLEAD.search(pre)
        if not x:
            problems.append('no "another K run the phone\'s node code" in the README\'s lead')
        else:
            if int(x.group(1)) != k:
                problems.append(f"the lead says another {x.group(1)} run the node's code; the count is {k}")
            pre = pre[:x.start(1)] + str(k) + pre[x.end(1):]
            m = LEAD.search(pre)
    word = fraction(w, t)
    said = " ".join(m.group(1).split())
    if said != word:
        problems.append(f'the lead says "{said}"; {w} of {t} ({100 * w // t}%) gives "{word}"')
    if (int(m.group(2)), int(m.group(3))) != (w, t):
        problems.append(f"the lead says {m.group(2)} of {m.group(3)}; the count is {w} of {t}")
    note = f", not counting {c} negative controls" if c else ""
    if (m.group(4) or "") != note and " ".join((m.group(4) or "").split()) != note:
        problems.append(f"the lead's count should say{note or ' nothing of negative controls'}")
    new = (pre[:m.start(1)] + word + pre[m.end(1):m.start(2)] + str(w) + pre[m.end(2):m.start(3)] + str(t)
           + note + pre[m.end(4) if m.group(4) else m.end(3):])
    return problems, new


def controls(rows, resolve):
    """The negative controls: notes marking a model law wired, or a World
    law, a ✅ row citing only a model law, a 🟡 row saying nothing missing,
    and a lead whose fraction is one step above the count's, or whose World
    count is off by one, must each fail."""
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
    world = next((f[1] for f in rows if f[0] == "law" and f[2] == "world"), None)
    if world:
        with open(path, "w") as f:
            f.write(open(NOTES).read() + f"\nwired {world}\n")
        _, caught = classify(path)
        if not any(f"marks {world} wired, but it is not" in p for p in caught):
            problems.append(f"negative control: {world}, a World law marked wired, was not caught")
    a_wired = sorted(wired)[0]
    rows_ = (f"| ✅ | 🥊 | **Control.** | [`{model}`] |\n"
             f"| 🟡 | 🥊 | **Control.** Proven. | [`{a_wired}`] |\n")
    if len(disagree(rows_, wired, lambda l: l)) != 2:
        problems.append("negative control: a ✅ row citing only a model law, or a 🟡 row "
                        "saying nothing missing, was not caught")
    c = sum(1 for f in rows if f[0] == "law" and f[2] == "control")
    w, t = len(wired), sum(1 for f in rows if f[0] == "law") - c
    k = sum(1 for f in rows if f[0] == "law" and f[2] == "world")
    words = [word for _, word in FRACTIONS]
    right = fraction(w, t)
    above = words[max(words.index(right) - 1, 0)] if right in words else "half"
    if not lead(f"about {above} of its theorems ({w} of {t}); another {k} run the phone's node code", w, t, k, c)[0]:
        problems.append(f'negative control: "{above}" for {w} of {t} was not caught')
    if not lead(f"about {right} of its theorems ({w} of {t}); another {k + 1} run the phone's node code", w, t, k, c)[0]:
        problems.append(f"negative control: another {k + 1} for {k} World laws was not caught")
    if not problems:
        print(f"proof-links: negative controls: {model} and {world} marked wired, a ✅ row citing only "
              f'a model law, a 🟡 row saying nothing missing, "{above}" for {w} of {t}, and another '
              f"{k + 1} for {k} World laws, all caught")
    return problems


def section(rows, decls, cited):
    """The README's todo section, from tests/Wiring.lean's lines."""
    laws = [(f[1], f[2], split(f[4]), split(f[5]), f[6], split(f[7])) for f in rows if f[0] == "law"]
    stmts = [(f[1], f[2], split(f[4])) for f in rows if f[0] == "stmt"]
    missing = {f[1]: (int(f[2]), f[3], split(f[4])) for f in rows if f[0] == "missing"}
    worldly = {f[1] for f in rows if f[0] == "missing" and len(f) > 5 and f[5] == "true"}
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
        """A row's place: the World's first, then tests/wiring.txt's order."""
        t = target(m, notes_of)
        return (-1 if t in worldly else missing[t][0] if t in missing and missing[t][1] else 10 ** 6, t)

    def link(n, mark="", cite=True):
        """A reference; of two parts when its last is short (`Symbolic.good`)."""
        label = short(n, decls, 1 if len(n.split(".")[-1]) > 4 else 2)
        return f"[`{label}`]" + mark + ("†" if cite and n in cited else "")

    def links(ls, cap=12):
        """A row's laws, `cap` at most."""
        more = f" +{len(ls) - cap} more" if len(ls) > cap else ""
        return ", ".join(link(n, mk) for n, mk in list(ls.items())[:cap]) + more

    def codes(t, names):
        """A row's definitions, its own first, three at most."""
        ns = [t] + sorted(names - {t}) if t in names else sorted(names)
        more = f" +{len(ns) - 3}" if len(ns) > 3 else ""
        return ", ".join(f"`{short(n, missing, 2)}`" for n in ns[:3]) + more

    # per area
    def area(mod):
        return next((a for p, a in AREAS if mod == p or mod.startswith(p + ".")), "Other")
    controls = [n for n, st, *_ in laws if st == "control"]
    laws = [l for l in laws if l[1] != "control"]  # out of the count
    per = {}
    for name, status, _, _, mod, _ in laws:
        c = per.setdefault(area(mod), [0, 0, 0])
        c[["wired", "world", "model"].index(status)] += 1
    order = list(dict.fromkeys([a for _, a in AREAS] + ["Other"]))
    stated = {}
    for n, st, _ in stmts:
        if st == "stated":
            stated[n.rsplit(".", 1)[0]] = stated.get(n.rsplit(".", 1)[0], 0) + 1
    out = [f"**{count['wired']} of {len(laws)} laws are about running code;** another {count['world']} "
           f"run its node code in a World, and {count['model']} are not yet. Stated only: "
           + (", ".join(f"{k} in `{m}`" for m, k in stated.items()) if stated else "none") + ". "
           f"{len(controls)} laws are negative controls: each proves a mutant breaks its law "
           "(they are not counted here, nor in the lead).", "",
           "| Area | Laws | About running code | In a World | Not yet |", "|---|---|---|---|---|"]
    for a in order:
        if a in per:
            w, W, m = per[a]
            out.append(f"| {a} | {w + W + m} | {w} | {W or ''} | {m or ''} |")
    # per missing link: a model, or running code a law restates
    copies = {f[1]: f[2] for f in rows if f[0] == "copy"}
    copied = {code: n for n, code in copies.items()}
    groups, general, inworld = {}, [], {}
    for name, status, miss, _, _, prem in laws:
        if not miss and status == "model":
            general.append(name)
            continue
        for m in (prem if status == "wired" else miss):
            t = place(m)[1]
            g = groups.setdefault(t, ({}, set()))
            g[1].add(m)
            if status == "world":  # counted, not listed
                inworld.setdefault(t, set()).add(name)
                continue
            g[0][name] = "°" if status == "wired" else "*" if set(miss) <= set(prem) else ""
    out += ["", "| Missing link | Laws | To make them real |", "|---|---|---|"]
    for t in sorted(groups, key=lambda t: place(t)):
        ls, names = groups[t]
        note = missing[t][1] if t in missing and missing[t][1] else ""
        if not note:
            by = sorted({c for n in names for c in missing.get(n, (0, "", []))[2]} - names)
            note = "Nothing that runs calls it" + (f"; {codes(by[0], set(by))} do" if by else "") + "."
        what = codes(t, names)
        if t in copied:  # running code a law restates
            what = f"restates `{short(t, [t], 2)}`"
        elif t in copies:  # a definition that restates running code
            what += f" (restates `{short(copies[t], [copies[t]], 2)}`)"
        cell = links(ls)
        if t in inworld:
            cell = f"{len(inworld[t])} World laws" + (f"; not yet: {cell}" if ls else "")
        out.append(f"| {what} | {cell} | {note} |")
    if general:
        out.append(f"| (none) | {links({n: '' for n in general})} | Nothing to wire: each is about "
                   "a specification or an assumption. |")
    out += ["", "\\* only a premise names it. ° about running code, but names it beside. "
            "† a guarantee above cites it.", "",
            "| Assumption | Laws | |", "|---|---|---|"]
    for a, text in assumed.items():
        if text.startswith("= "):
            continue
        part = [a] + [b for b in assumed if b != a and target(b, assumed) == a]
        n = sum(1 for law in laws if set(law[3]) & set(part))
        out.append(f"| {link(a, cite=False)} | {n} | {text} |")
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
    problems += disagree(tables, wired, resolve)
    # the lead's fraction and count, and "nearly every" only at the threshold
    ncontrol = sum(1 for f in rows if f[0] == "law" and f[2] == "control")
    stale, pre_new = lead(pre, len(wired), total - ncontrol,
                          sum(1 for f in rows if f[0] == "law" and f[2] == "world"), ncontrol)
    if check or not LEAD.search(pre):
        problems += stale
    pre = pre_new
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
