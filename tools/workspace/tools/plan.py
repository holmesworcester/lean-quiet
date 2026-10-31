#!/usr/bin/env python3
"""Plan the op tree from main's actual sources.

Reads layout/tree.json (the target folders and where each of today's files
goes) and the repository's Lean sources, and writes the plan the workspace
draws: every target file's contents as fragments of today's code, with
where each fragment comes from.

- `split` files (a family's types) are cut by constructor: each op's
  cases go to its Op.lean, its validator cases to its Validate.lean.
- `place` files are cut by top-level declaration: each one goes to the
  common ancestor of the deepest ops it names (a theorem by its
  statement, a definition by its body). What names no op stays in `rest`.
- Every other file moves whole.

Usage: plan.py [--check] [--write-tree PATH] [--out PATH]
"""
from pathlib import Path
import json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
LAYOUT = json.loads((ROOT / 'layout/tree.json').read_text())
RUN = lambda *a: subprocess.check_output(a, cwd=REPO, text=True).strip()

REQUIRED = ['Op.lean', 'Validate.lean', 'Proofs.lean', 'Tests.lean']
ORDER = ['Op.lean', 'Validate.lean', 'View.lean', 'Commands.lean', 'Screen.lean', 'Proofs.lean', 'Tests.lean', 'Family.lean']
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)\b\s*([^\s:(\[{]*)')

def read(path):
    return (REPO / path).read_text()

def tracked():
    return RUN('git', 'ls-files').splitlines()

# --- Nodes -----------------------------------------------------------------

nodes = {n['path']: dict(n) for n in LAYOUT['nodes']}
for path, n in nodes.items():
    n['name'] = path.split('/')[-1]
    n['parent'] = path.rsplit('/', 1)[0] if '/' in path else None
    n['children'] = [p for p in nodes if p.rsplit('/', 1)[0] == path and p != path]
    n['kind'] = 'op' if ('op' in n or n.get('planned')) else 'group'
    n['canonical'] = '.'.join(path.split('/')[1:]) or 'app'

def ancestors(path):
    out = []
    while path:
        out.append(path)
        path = nodes[path]['parent']
    return out

def lca(paths):
    common = None
    for p in paths:
        chain = list(reversed(ancestors(p)))
        common = chain if common is None else [a for a, b in zip(common, chain) if a == b]
    return common[-1] if common else 'app'

def home(paths):
    """The common ancestor of the deepest named ops: a folder sees the ops it cites (its ancestors)."""
    paths = set(paths)
    if not paths:
        return None
    leaves = [p for p in paths if not any(q != p and p in ancestors(q) for q in paths)]
    return lca(leaves)

# --- Tokens: which op a constructor or relation names ----------------------

ops = {p: n['op'] for p, n in nodes.items() if 'op' in n}
fam_tokens = {}  # family -> token -> set of node paths
for path, op in ops.items():
    fam = op['family']
    t = fam_tokens.setdefault(fam, {})
    if 'body' in op:
        t.setdefault(('body', op['body']), set()).add(path)
    for f in op.get('facts', []):
        t.setdefault(('fact', f), set()).add(path)
    for r in op.get('rels', []):
        t.setdefault(('rel', r), set()).add(path)

def shallowest(paths):
    return min(paths, key=lambda p: (len(ancestors(p)), p))

def family_of(source):
    for fam in ('connection', 'community', 'sync'):
        if source.startswith(f'ops/{fam}/'):
            return fam
    return 'community'

# A definition placed in an op's folder (a composer like `react`) names that op wherever it is called.
calls = {}

def mentions(text, source):
    """Op nodes a piece of Lean names, resolving shared names to the file's own family."""
    own = family_of(source)
    found = {home for (fam, name), home in calls.items() if fam == own and re.search(rf'(?<![\w.]){re.escape(name)}\s+[\w(⟨]', text)}
    order = [own] + [f for f in fam_tokens if f != own]
    seen_names = set()
    for fam in order:
        for (kind, name), paths in fam_tokens[fam].items():
            if (kind, name) in seen_names:
                continue
            if kind == 'rel':
                pat = rf'(?<![\w.]){re.escape(name)}\.[a-z]\w*'
            else:
                ns = 'Body' if kind == 'body' else 'Fact'
                pat = rf'(?:(?<![\w.\)\]\'!?])\.{re.escape(name)}\b|\b{ns}\.{re.escape(name)}\b)'
            if re.search(pat, text):
                found.add(shallowest(paths))
                if fam == own:
                    seen_names.add((kind, name))
        # Names in the file's own family shadow the same names elsewhere.
    return found

# --- Lean structure ---------------------------------------------------------

def blocks(text):
    """Top-level blocks: (kind, name, start, end) with a leading docstring attached."""
    lines = text.split('\n')
    starts = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = DECL.match(line)
        if m:
            s = i
            j = i - 1
            if j >= 0 and lines[j].rstrip().endswith('-/'):
                while j >= 0 and not lines[j].lstrip().startswith('/--'):
                    j -= 1
                if j >= 0:
                    s = j
            starts.append((m.group(1), m.group(2), s, i))
        i += 1
    out = []
    for k, (kind, name, s, d) in enumerate(starts):
        e = (starts[k + 1][2] if k + 1 < len(starts) else len(lines))
        while e > d + 1 and (not lines[e - 1].strip() or re.match(r'^(end|namespace|section|open|variable|set_option|/-!)', lines[e - 1])):
            e -= 1
        out.append((kind, name, s, e))
    return out, lines

def statement(text):
    text = re.sub(r'^\s*/--.*?-/\s*', '', text, flags=re.S)
    m = re.search(r':=\s*by\b|:=\s*$|:=\s', text, re.M)
    return text[:m.start()] if m else text

# --- Fragments --------------------------------------------------------------

fragments = {}   # target file -> list of fragments
taken = {}       # source -> set of line numbers (1-based) assigned to a target

def add(target, source, start, end, label, lines):
    fragments.setdefault(target, []).append({
        'from': source, 'start': start + 1, 'end': end, 'label': label,
        'text': '\n'.join(lines[start:end]).rstrip('\n'),
    })
    taken.setdefault(source, set()).update(range(start + 1, end + 1))

def split_family(source, fam, rest):
    text = read(source)
    lines = text.split('\n')
    tokens = fam_tokens[fam]
    body_tag, fact_tag = {}, {}
    # Tags from the encoders: `| .ctor ... => N ::` or `=> [N]`.
    current = None
    for l in lines:
        d = re.match(r'^def (Body|Fact)\.enc\b', l)
        if d:
            current = d.group(1)
            continue
        if current and l and not l.startswith(' '):
            current = None
        m = current and re.match(r'\s+\| \.(\w+)\b.*?=>\s*\[?(\d+)', l)
        if m:
            (body_tag if current == 'Body' else fact_tag).setdefault(int(m.group(2)), m.group(1))
    def owner(kind, name):
        paths = tokens.get((kind, name))
        return shallowest(paths) if paths else None
    bl, _ = blocks(text)
    for kind, name, s, e in bl:
        head = lines[s:e]
        ns = 'Fact' if name.startswith('Fact.') or (kind == 'inductive' and name == 'Fact') else 'Body'
        is_check = kind == 'def' and name == LAYOUT['families'][fam]['check']
        role = 'Validate.lean' if is_check else 'Op.lean'
        i = s
        pending = None
        cases = []  # (owner, start, end)
        while i < e:
            l = lines[i]
            if re.match(r'^\s+--', l) and pending is None:
                pending = i
            m = re.match(r'^(\s+)\| (.*)', l)
            if m and len(m.group(1)) <= 4:
                pat = m.group(2)
                who = None
                c = re.match(r'(\w+)\b', pat) if kind == 'inductive' else re.match(r'(?:\.(\w+)|(\d+) ::|some (\d+) =>)', pat)
                if c and pat.count('| .') == 0:
                    if c.group(1):
                        who = owner('fact' if ns == 'Fact' else 'body', c.group(1))
                        if who is None:
                            who = owner('body' if ns == 'Fact' else 'fact', c.group(1))
                    else:
                        tag = int(c.group(2) or c.group(3))
                        ctor = (fact_tag if ns == 'Fact' else body_tag).get(tag)
                        if ctor:
                            who = owner('fact' if ns == 'Fact' else 'body', ctor)
                j = i + 1
                while j < e and lines[j].startswith(m.group(1) + ' ') and lines[j].strip():
                    j += 1
                start = pending if pending is not None else i
                if who:
                    cases.append((who, start, j))
                pending = None
                i = j
                continue
            if not re.match(r'^\s+--', l):
                pending = None
            i += 1
        for who, a, b in cases:
            add(f'{who}/{role}', source, a, b, name, lines)
    # Relations: `namespace <fact kind>` ... `end <fact kind>`.
    for i, l in enumerate(lines):
        m = re.match(r'^namespace (\w+)$', l)
        if m and ('rel', m.group(1)) in tokens:
            j = i + 1
            while j < len(lines) and lines[j] != f'end {m.group(1)}':
                j += 1
            add(f"{owner('rel', m.group(1))}/Op.lean", source, i, j + 1, f'{m.group(1)}.*', lines)
    remainder(source, rest, lines)

def place(source, role, rest):
    text = read(source)
    bl, lines = blocks(text)
    for kind, name, s, e in bl:
        chunk = '\n'.join(lines[s:e])
        named = mentions(statement(chunk) if kind in ('theorem', 'lemma') else chunk, source)
        target_role = 'Proofs.lean' if kind in ('theorem', 'lemma') else role
        h = home(named)
        if h:
            add(f'{h}/{target_role}', source, s, e, name, lines)
            fragments[f'{h}/{target_role}'][-1]['names'] = sorted(named)
            if kind == 'def' and 'op' in nodes[h] and name and '.' not in name:
                calls[(family_of(source), name)] = h
    remainder(source, rest, lines)

def remainder(source, target, lines):
    used = taken.get(source, set())
    runs, start = [], None
    for n in range(1, len(lines) + 1):
        free = n not in used
        if free and start is None:
            start = n
        if not free and start is not None:
            runs.append((start, n - 1)); start = None
    if start is not None:
        runs.append((start, len(lines)))
    for a, b in runs:
        seg = lines[a - 1:b]
        if any(s.strip() for s in seg):
            add(target, source, a - 1, b, 'rest', lines)

def whole(source, target):
    lines = read(source).split('\n')
    add(target, source, 0, len(lines), 'file', lines)

files = [f for f in tracked() if f.endswith('.lean')]
scope = [f for f in files if f.startswith('ops/') or f in ('App.lean', 'AppTypes.lean', 'AppLife.lean')]
moves = {}
for source in sorted(set(scope) | {s for s in LAYOUT['sources'] if not s.endswith('/')}):
    rule = LAYOUT['sources'].get(source)
    if rule is None:
        rule = next((t for k, t in LAYOUT['sources'].items() if k.endswith('/') and source.startswith(k)), None)
    if rule is None:
        moves[source] = None
        continue
    if isinstance(rule, str):
        whole(source, rule)
        moves[source] = [rule]
    elif 'split' in rule:
        split_family(source, rule['split'], rule['rest'])
    else:
        place(source, rule['place'], rule['rest'])
    if not isinstance(rule, str):
        moves[source] = sorted({t for t, fr in fragments.items() for f in fr if f['from'] == source})

# --- Files per folder --------------------------------------------------------

engine_moves = {t: s for s, t in LAYOUT['sources'].items() if isinstance(t, str) and t.startswith('engine/')}
for t in list(fragments):
    if t.startswith('engine/'):
        continue
    folder = t.rsplit('/', 1)[0]
    if folder not in nodes:
        raise SystemExit(f'{t}: no folder {folder} in layout/tree.json')

for path, n in nodes.items():
    present = {t.rsplit('/', 1)[1] for t in fragments if t.rsplit('/', 1)[0] == path}
    names = set(present)
    if n['kind'] == 'op':
        names |= set(REQUIRED)
        if n.get('view'):
            names.add('View.lean')
    if n['children']:
        names.add('Family.lean')
    if n.get('screen'):
        names.add('Screen.lean')
    n['files'] = [f for f in ORDER if f in names]
    unknown = names - set(ORDER)
    if unknown:
        raise SystemExit(f'{path}: files outside the vocabulary: {sorted(unknown)}')

# --- Tests today that exercise each op ---------------------------------------

test_files = [f for f in files if f.startswith(('tests/', 'platforms/headless/'))]
test_text = {f: read(f) for f in test_files}
for path, op in ops.items():
    if 'body' not in op:
        continue
    pat = re.compile(rf'(?<![\w.\)\]])\.{re.escape(op["body"])}\b|\bBody\.{re.escape(op["body"])}\b')
    need = 'Connection' if op['family'] == 'connection' else ''
    nodes[path]['tests'] = sorted(f for f, t in test_text.items() if need in t and pat.search(t))[:12]

# --- Requirements: what each validator case cites ---------------------------

for path, op in ops.items():
    frs = fragments.get(f'{path}/Validate.lean', [])
    slots = []
    for fr in frs:
        m = re.match(r'\s*(?:--[^\n]*\n\s*)*\| \.\w+[^,]*,\s*(\[[^\]]*\]|[^=]*?)\s*=>', fr['text'], re.S)
        if m:
            cited = re.findall(r'\.(\w+)', m.group(1))
            refs = []
            for c in cited:
                paths = fam_tokens[op['family']].get(('fact', c)) or fam_tokens.get('community', {}).get(('fact', c))
                if paths:
                    refs.append({'fact': c, 'producers': sorted(paths, key=lambda p: (len(ancestors(p)), p))})
            slots.append(refs)
    nodes[path]['requires'] = slots

# --- Imports that cross: a moved file importing a module that lands elsewhere ---

module_home = {}
for source, targets in moves.items():
    if targets:
        module_home[source[:-5].replace('/', '.')] = targets
for target, frs in fragments.items():
    for fr in frs:
        if fr['label'] != 'file':
            continue
        imports = re.findall(r'^import (\S+)', fr['text'], re.M)
        folder = target.rsplit('/', 1)[0]
        cross = []
        for imp in imports:
            if imp.startswith('engine.') or imp.startswith('Std') or imp.startswith('Lean') or imp.startswith('Init'):
                continue
            for t in module_home.get(imp, []):
                f = t.rsplit('/', 1)[0]
                if t.startswith('engine/') or f == folder or f in ancestors(folder) or folder in ancestors(f):
                    continue
                cross.append({'module': imp, 'lands': t})
        if cross:
            fr['crosses'] = cross

# --- Engine and platforms -----------------------------------------------------

def tree_listing(prefix):
    out = []
    for f in files:
        if f.startswith(prefix):
            text = read(f)
            imports = re.findall(r'^import (\S+)', text, re.M)
            names = [i for i in imports if i.startswith('ops.') or i in ('App', 'AppTypes', 'AppLife')]
            out.append({'path': f, 'lines': text.count('\n') + 1, 'namesKinds': names,
                        'leaves': LAYOUT['sources'].get(f)})
    return out

engine = tree_listing('engine/') + [{'path': t, 'lines': 0, 'namesKinds': [], 'arrives': s} for t, s in engine_moves.items()]
engine.sort(key=lambda e: e['path'])
platforms = tree_listing('platforms/')

laws = []
for target, frs in fragments.items():
    for fr in frs:
        if target.endswith('/Proofs.lean') and fr['label'] not in ('rest', 'file'):
            m = re.match(r'(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?(theorem|lemma)\b', fr['text'], re.S)
            if m:
                laws.append({'name': fr['label'], 'target': target, 'from': fr['from'], 'line': fr['start']})

revision = RUN('git', 'rev-parse', 'HEAD')
try:
    base = RUN('git', 'merge-base', 'HEAD', 'origin/main')
except subprocess.CalledProcessError:
    base = revision

plan = {
    'base': base, 'revision': revision, 'repository': 'holmesworcester/lean-quiet',
    'roles': LAYOUT['roles'], 'nodes': [nodes[p] for p in nodes],
    'fragments': fragments, 'moves': moves, 'laws': laws,
    'engine': engine, 'platforms': platforms,
}

def tree_text():
    out = ['app/']
    def visit(path, indent):
        n = nodes[path]
        entries = [(None, c) for c in sorted(n['children'], key=lambda c: nodes[c]['name'])] + [(f, None) for f in n['files']]
        for k, (f, c) in enumerate(entries):
            last = k == len(entries) - 1
            mark = '└── ' if last else '├── '
            if f:
                status = '' if f'{path}/{f}' in fragments else '   (planned)'
                out.append(f'{indent}{mark}{f}{status}')
            else:
                planned = '   (planned op)' if nodes[c].get('planned') else ''
                out.append(f'{indent}{mark}{nodes[c]["name"]}/{planned}')
                visit(c, indent + ('    ' if last else '│   '))
    visit('app', '')
    return ('Lean Quiet: the op tree (target layout)\n'
            f'Generated by tools/workspace/tools/plan.py from main {base[:12]}.\n'
            'Every file shows where its code is today in the workspace.\n\n' + '\n'.join(out) + '\n')

if __name__ == '__main__':
    args = sys.argv[1:]
    unplaced = [s for s, t in moves.items() if t is None]
    if unplaced:
        raise SystemExit('No destination in layout/tree.json for: ' + ', '.join(unplaced))
    if '--out' in args:
        Path(args[args.index('--out') + 1]).write_text(json.dumps(plan, ensure_ascii=False))
    if '--write-tree' in args:
        Path(args[args.index('--write-tree') + 1]).write_text(tree_text())
    if '--check-tree' in args:
        path = Path(args[args.index('--check-tree') + 1])
        if not path.exists() or path.read_text() != tree_text():
            raise SystemExit(f'{path} is stale. Run mise run workspace:layout.')
    if not args:
        print(tree_text())
