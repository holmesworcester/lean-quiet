#!/usr/bin/env python3
"""docs/PROOF-TREE.md: how the laws compose, drawn from the build.

tests/Wiring.lean, given WIRING_GRAPH=path, writes the graph: each
theorem written by hand in the modules tests/Axioms.lean imports, with
its class (an audited law's, as tests/Wiring.lean classifies it; `lemma`
for the rest), module and line, the laws its proof uses, and a step's
wired users. ci/proof-links.py's run of it writes out/proof-graph.json.
From the graph and the README this draws:

- **The scoreboard:** laws, edges (a proof uses a law), roots (laws no
  law uses), isolated (roots that use no law either), the deepest and
  the median chain, and the share of laws the headlines build on.
  Composition shows here: roots and isolated laws go down, reach up.
- **The headlines:** the laws the README cites, under its headings and
  table groups, each the tree of the laws it builds on. A law is drawn
  whole once (a headline where it is cited, any other where it is first
  met), and links there elsewhere. A subtree DEPTH levels down is drawn
  under "Deeper", once.
- **The uncited roots,** by folder: laws no law uses and the README does
  not cite. The flat forest, which later work composes or deletes.

  ci/proof-tree.py            write docs/PROOF-TREE.md (runs tests/Wiring.lean)
  ci/proof-tree.py --check    fail if it is stale, or a file of it is not
                              tracked. Negative control: the doc drawn from
                              the graph less one edge must differ from it
  --graph PATH                draw this graph instead of running
                              tests/Wiring.lean (ci/proof-links.py passes
                              the one its run wrote)

The doc holds no time and no commit: the same build draws the same doc.
An unknown class fails, rather than being drawn as a guess. Tests:
tests/proof_tree_test.py.
"""
import importlib.util
import json
import os
import posixpath
import re
import statistics
import subprocess
import sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = os.path.join(TOP, "docs")
INDEX, ALSO = "PROOF-TREE.md", "proof-tree/also-cited.md"
WRITTEN = "written by ci/proof-tree.py from tests/Wiring.lean's graph; do not edit"
GRAPH = os.path.join(TOP, "out", "proof-graph.json")
README = os.path.join(TOP, "README.md")
# How many levels a headline's tree nests before "Deeper" takes over.
DEPTH = 5
BADGE = {"wired": "✅", "world": "🌐", "step": "🪜", "model": "📐", "control": "🧪", "lemma": "▫️"}
MEANS = {"wired": "about running code", "world": "the node's code in a World",
         "step": "a step of a wired law", "model": "over a model",
         "control": "a negative control", "lemma": "not audited"}
REF = re.compile(r"\[`([^`\]]+)`\](?![(\[])")  # a shortcut reference, as ci/proof-links.py reads it


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


LINKS = load_module("proof_links", os.path.join(TOP, "ci", "proof-links.py"))
VACUITY = load_module("vacuity", os.path.join(TOP, "ci", "vacuity.py"))
# the README's generated blocks: what they cite is not a headline
GENERATED = [(LINKS.WBEGIN, LINKS.WEND), (VACUITY.BEGIN, VACUITY.END), (LINKS.BEGIN, LINKS.END)]


class Graph:
    """The laws, what each uses and is used by, and what each builds on."""

    def __init__(self, laws):
        self.law = {}
        for l in laws:
            if l["class"] not in BADGE:
                raise ValueError(f"unknown class {l['class']!r} of {l['name']}: teach ci/proof-tree.py its badge")
            self.law[l["name"]] = l
        self.uses = {n: sorted(set(l["uses"]) - {n}) for n, l in self.law.items()}
        self.users = {n: [] for n in self.law}
        for n, ds in sorted(self.uses.items()):
            for d in ds:
                if d not in self.law:
                    raise ValueError(f"{n} uses {d}, which the graph does not hold")
                self.users[d].append(n)
        self.index = {n: i for i, n in enumerate(sorted(self.law))}
        self.below, self.depth = {}, {}
        for n in self.order():  # each law after those it uses
            mask, deep = 0, 0
            for d in self.uses[n]:
                mask |= (1 << self.index[d]) | self.below.get(d, 0)  # a cycle: d not done yet
                deep = max(deep, self.depth.get(d, 0) + 1)
            self.below[n], self.depth[n] = mask, deep

    def order(self):
        """The laws, each after the laws it uses (a depth-first walk in
        name order; a cycle is cut where the walk meets it again)."""
        seen, out = set(), []
        for root in sorted(self.law):
            if root in seen:
                continue
            seen.add(root)
            stack = [(root, iter(self.uses[root]))]
            while stack:
                n, it = stack[-1]
                for d in it:
                    if d not in seen:
                        seen.add(d)
                        stack.append((d, iter(self.uses[d])))
                        break
                else:
                    stack.pop()
                    out.append(n)
        return out

    def size(self, n):
        """How many laws n builds on."""
        return bin(self.below[n]).count("1")

    def without(self, n, d):
        """The graph less the edge n → d."""
        laws = [dict(l, uses=[x for x in l["uses"] if not (l["name"] == n and x == d)]) for l in self.law.values()]
        return Graph(laws)


def load(path):
    with open(path) as f:
        return Graph(json.load(f)["laws"])


def citations(readme, g):
    """The laws the README cites, outside its generated blocks, by heading
    and table group, in its order: those its guarantee rows cite (a ✅, 🟡
    or ⬜ row, as ci/proof-links.py checks them), and those it cites
    elsewhere, each [(section, [law])]."""
    for begin, end in GENERATED:
        if begin in readme and end in readme:
            head, rest = readme.split(begin, 1)
            readme = head + rest.split(end, 1)[1]
    audited = [n for n, l in g.law.items() if l["class"] != "lemma"]
    resolve = LINKS.resolver(audited + LINKS.ASSUMED)
    rows, prose, head, group, fence = {}, {}, "README", None, False
    for line in readme.split("\n"):
        if line.startswith("```"):
            fence = not fence
        if fence:
            continue
        m = re.match(r"#{1,4} (.+)", line)
        if m:
            head, group = m.group(1).strip(), None
            continue
        t = re.match(r"\|\s*\|\s*\|\s*\*\*(.+?)\*\*\s*\|", line)
        if t:
            group = t.group(1).strip().rstrip(".")
            continue
        if line.strip() and not line.startswith("|"):
            group = None
        row = line.startswith("|") and line.strip("| ").startswith(("✅", "🟡", "⬜"))
        for label in REF.findall(line):
            n = resolve(label)
            if n in g.law:
                laws = (rows if row else prose).setdefault(f"{head} › {group}" if group else head, [])
                if n not in laws:
                    laws.append(n)
    return list(rows.items()), list(prose.items())


def metrics(g, cited):
    """The scoreboard, as (name, value) rows."""
    n = len(g.law)
    roots = [x for x in g.law if not g.users[x]]
    isolated = [x for x in roots if not g.uses[x]]
    depths = list(g.depth.values())
    reach = 0
    for c in cited:
        reach |= (1 << g.index[c]) | g.below[c]
    r = bin(reach).count("1")
    pct = lambda k: f"{100 * k / n:.1f}%" if n else "0%"
    return [("Laws", f"{n}"), ("Edges (a proof uses a law)", f"{sum(len(u) for u in g.uses.values())}"),
            ("Roots (no law uses them)", f"{len(roots)} ({pct(len(roots))})"),
            ("Isolated (roots that use no law)", f"{len(isolated)} ({pct(len(isolated))})"),
            ("Deepest chain", f"{max(depths, default=0)}"),
            ("Median chain", f"{statistics.median(depths) if depths else 0:g}"),
            ("Headlines (laws the README's guarantee rows cite)", f"{len(cited)}"),
            ("Laws the headlines build on, or are", f"{r} ({pct(r)})")]


def folder(module):
    parts = module.split(".")
    return "/".join(parts[:-1]) or parts[0]


def display(name):
    """A private law's name as written."""
    return re.sub(r"^_private\.(?:.*?)\.0\.", "", name)


def slug(section):
    return re.sub(r"[^a-z0-9]+", "-", section.lower()).strip("-")


class Drawing:
    """The trees, each law drawn whole once, in the file where its
    headline is, or where it is first met."""

    def __init__(self, g, home):
        self.g = g
        self.anchor = {}
        used = set()
        for n in sorted(g.law):
            a = "law-" + re.sub(r"[^A-Za-z0-9_.-]", "-", display(n))
            while a in used:
                a += "-"
            used.add(a)
            self.anchor[n] = a
        self.home = dict(home)  # law -> the file it is drawn whole in
        self.file = INDEX
        self.top = set()
        self.deeper = []

    def name(self, n, href):
        return f'{BADGE[self.g.law[n]["class"]]} <a href="{href}">{display(n)}</a>'

    def source(self, n):
        l = self.g.law[n]
        return "../" * (self.file.count("/") + 1) + f'{l["module"].replace(".", "/")}.lean#L{l["line"]}'

    def link(self, n):
        """A law drawn whole elsewhere: its name, linked there."""
        h = self.home[n]
        where = "" if h == self.file else posixpath.relpath(h, posixpath.dirname(self.file) or ".")
        return f"<li>{self.name(n, where + '#' + self.anchor[n])} ↪{self.notes(n)}</li>"

    def notes(self, n):
        k = self.g.size(n)
        out = f" · {k} below" if k else ""
        users = self.g.law[n].get("users") or []
        if users:
            more = f" +{len(users) - 3}" if len(users) > 3 else ""
            out += " · a step of " + ", ".join(display(u) for u in users[:3]) + more
        return out

    def whole(self, n, level, out):
        """n's subtree: n, then each law it uses, the larger subtrees first."""
        head = f'<a id="{self.anchor[n]}"></a>{self.name(n, self.source(n))}{self.notes(n)}'
        if not self.g.uses[n]:
            out.append(f"<li>{head}</li>")
            return
        out.append(f"<li><details><summary>{head}</summary><ul>")
        for d in sorted(self.g.uses[n], key=lambda d: (-self.g.size(d), d)):
            self.node(d, level + 1, out)
        out.append("</ul></details></li>")

    def node(self, n, level, out):
        """A law met in a tree: drawn whole here if it is nowhere else."""
        if not self.g.uses[n]:  # a leaf: the same everywhere
            out.append(f"<li>{self.name(n, self.source(n))}{self.notes(n)}</li>")
        elif n in self.home:
            out.append(self.link(n))
        else:
            self.home[n] = self.file
            if level < DEPTH:
                self.whole(n, level, out)
            else:
                self.deeper.append(n)
                out.append(self.link(n))

    def headline(self, n, out):
        if n in self.top:  # cited again
            out.append(self.link(n))
        else:
            self.top.add(n)
            self.whole(n, 0, out)

    def page(self, file, title, groups, about):
        """A file of trees: a group of headlines each, then what is deeper."""
        self.file = file
        out = [f"# {title}", "", f"<!-- {WRITTEN} -->", "",
               f"[The proof tree](../PROOF-TREE.md): {about} Each opens to the laws its proof uses; "
               f"a law drawn whole elsewhere links there (↪), and a subtree {DEPTH} levels down "
               "continues under [Deeper](#deeper).", "", legend(self.g)]
        for heading, laws in groups:
            if heading:
                out += ["", f"## {heading}"]
            out += ["", "<ul>"]
            for n in laws:
                self.headline(n, out)
            out.append("</ul>")
        out += ["", "## Deeper", "", f"Subtrees met {DEPTH} levels down, drawn whole here once.", "", "<ul>"]
        while self.deeper:
            self.whole(self.deeper.pop(0), 0, out)
        out.append("</ul>")
        return "\n".join(out) + "\n"


def legend(g):
    classes = {c: sum(1 for l in g.law.values() if l["class"] == c) for c in BADGE}
    return " · ".join(f"{BADGE[c]} {c}: {MEANS[c]} ({classes[c]})" for c in BADGE)


def render(g, readme):
    """The doc's files, by their path under docs/: docs/PROOF-TREE.md,
    then a file of trees for each README table group, and one for the
    laws the README cites elsewhere."""
    sections, prose = citations(readme, g)
    cited = list(dict.fromkeys(n for _, laws in sections for n in laws))
    files = {}
    for section, _ in sections:
        f = f"proof-tree/{slug(section)}.md"
        while f in files.values() or f == ALSO:
            f = f[:-3] + "-.md"
        files[section] = f
    home = {}
    for section, laws in sections:
        for n in laws:
            home.setdefault(n, files[section])
    for _, laws in prose:
        for n in laws:
            home.setdefault(n, ALSO)
    d = Drawing(g, home)
    pages = {}
    for section, laws in sections:
        pages[files[section]] = d.page(files[section], section, [(None, laws)],
                                       f"the laws the README's rows cite under **{section}**.")
    pages[ALSO] = d.page(ALSO, "Also cited", prose, "the laws the README cites outside its guarantee rows.")
    drawn = {f: sum(1 for h in d.home.values() if h == f) for f in pages}
    # the index: the scoreboard, the files, the flat forest
    d.file = INDEX
    out = ["# The proof tree", "", f"<!-- {WRITTEN} -->", "",
           "How the laws compose: each law opens to the laws its proof uses. The headlines are the "
           "laws the [README](../README.md#what-is-proven)'s guarantee rows cite, each a tree in the "
           "file of its table group. A law is drawn whole once, and links there (↪) elsewhere; "
           "*n below* counts the distinct laws a law builds on.", "", legend(g), "",
           "## Scoreboard", "",
           "Composing the proofs into one tree lowers the roots and isolated laws, and raises the "
           "share the headlines build on.", "", "| | |", "|---|---|"]
    out += [f"| {k} | {v} |" for k, v in metrics(g, cited)]
    out += ["", "## Headlines", "", "| Group | Headlines | Laws drawn there |", "|---|---|---|"]
    out += [f"| [{s}]({files[s]}) | {len(laws)} | {drawn[files[s]]} |" for s, laws in sections]
    out.append(f"| [Also cited]({ALSO}) | {len(set(n for _, laws in prose for n in laws))} | {drawn[ALSO]} |")
    roots = [n for n in sorted(g.law) if not g.users[n] and n not in home]
    areas = {}
    for n in g.law:
        areas.setdefault(folder(g.law[n]["module"]), [0, [], 0])[0] += 1
    for n in roots:
        a = areas[folder(g.law[n]["module"])]
        a[1].append(n)
        a[2] += not g.uses[n]
    out += ["", "## Uncited roots", "",
            f"Laws no law uses and the README does not cite: {len(roots)}, "
            f"{sum(a[2] for a in areas.values())} of them isolated (they use no law either). "
            "Each is a claim of its own or a dead end; composing them into the headlines' "
            "trees, or deleting them, shrinks this list.", "",
            "| Folder | Laws | Uncited roots | Isolated |", "|---|---|---|---|"]
    out += [f"| {a} | {k} | {len(rs)} | {i} |" for a, (k, rs, i) in sorted(areas.items()) if rs]
    for a, (_, rs, _) in sorted(areas.items()):
        if rs:
            out += ["", f"<details><summary><b>{a}</b> · {len(rs)}</summary><ul>"]
            out += [f"<li>{d.name(n, d.source(n))}{d.notes(n) or ' · isolated'}</li>" for n in rs]
            out.append("</ul></details>")
    pages[INDEX] = "\n".join(out) + "\n"
    return dict(sorted(pages.items()))


def control(g, readme, pages):
    """The negative control: the graph less one edge draws another doc."""
    for _, laws in citations(readme, g)[0]:
        for n in laws:
            if g.uses[n]:
                return render(g.without(n, g.uses[n][0]), readme) != pages
    return False


def wiring_graph(path=GRAPH):
    """Run tests/Wiring.lean for its graph."""
    if os.path.exists(path):
        os.remove(path)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    r = subprocess.run(["lake", "env", "lean", "--run", "tests/Wiring.lean"], cwd=TOP,
                       capture_output=True, text=True, env=dict(os.environ, WIRING_GRAPH=path))
    if not os.path.exists(path):
        sys.exit(f"proof-tree: tests/Wiring.lean wrote no graph (is the tree built, and Main?)\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    return path


def written(docs):
    """The doc's files as they stand, by their path under docs/."""
    out = {}
    names = [INDEX] + [f"proof-tree/{f}" for f in sorted(os.listdir(os.path.join(docs, "proof-tree")))
                       if f.endswith(".md")] if os.path.isdir(os.path.join(docs, "proof-tree")) else [INDEX]
    for f in names:
        if os.path.exists(os.path.join(docs, f)):
            with open(os.path.join(docs, f)) as h:
                out[f] = h.read()
    return out


def main(argv):
    check = "--check" in argv
    arg = lambda flag, default: argv[argv.index(flag) + 1] if flag in argv else default
    docs, readme_path = arg("--docs", DOCS), arg("--readme", README)
    graph = arg("--graph", None) or wiring_graph()
    if not os.path.exists(graph):
        print(f"proof-tree: no graph at {graph} (ci/proof-links.py writes it)")
        return 1
    g = load(graph)
    with open(readme_path) as f:
        readme = f.read()
    pages = render(g, readme)
    if not check:
        os.makedirs(os.path.join(docs, "proof-tree"), exist_ok=True)
        for f in written(docs):
            if f not in pages:
                os.remove(os.path.join(docs, f))
        for f, text in pages.items():
            with open(os.path.join(docs, f), "w") as h:
                h.write(text)
        print(f"proof-tree: wrote docs/{INDEX} and {len(pages) - 1} files in docs/proof-tree")
        return 0
    problems = []
    old = written(docs)
    stale = sorted(f for f in set(old) | set(pages) if old.get(f) != pages.get(f))
    if stale:
        more = f" and {len(stale) - 3} more" if len(stale) > 3 else ""
        problems.append(f"stale: {', '.join('docs/' + f for f in stale[:3])}{more}: "
                        "run ci/proof-links.py (or ci/proof-tree.py)")
    if docs == DOCS:  # a new group's file must be committed with the rest
        tracked = subprocess.run(["git", "ls-files", "docs/" + INDEX, "docs/proof-tree"], cwd=TOP,
                                 capture_output=True, text=True).stdout.split()
        new = sorted(f"docs/{f}" for f in pages if f"docs/{f}" not in tracked)
        if new:
            problems.append(f"not tracked: git add {' '.join(new)}")
    if not control(g, readme, pages):
        problems.append("negative control: the graph less one edge draws the same doc")
    for p in problems:
        print("proof-tree:", p)
    if not problems:
        print(f"proof-tree: docs/{INDEX} and docs/proof-tree are current ({len(g.law)} laws); "
              "negative control (one edge less) caught")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
