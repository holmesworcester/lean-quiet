#!/usr/bin/env python3
"""The op tree on disk, with what is planned in it.

Reads every tracked file under app/ and layout/tree.json, and writes the
plan the workspace draws: each folder (an op, a family, or a planned op or
family) and each file with its text. tree.json gives folders their
summaries and previews and names the planned ones; it never names code.

A file is planned when LAYOUT02 requires it and it is not on disk: an op's
Op, Validate, Proofs and Tests, its View or Screen when tree.json says so,
and Family at a family's root (a folder right under app/ with child folders:
docs/OP_WORKSPACE_REQUIREMENTS.md, recorded exceptions).

Usage: plan.py [--layout PATH] [--out PATH] [--write-tree PATH] [--check-tree PATH]
"""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ORDER = ['Op.lean', 'Validate.lean', 'View.lean', 'Commands.lean', 'Screen.lean', 'Proofs.lean', 'Tests.lean', 'Family.lean']
REQUIRED = ['Op.lean', 'Validate.lean', 'Proofs.lean', 'Tests.lean']
OUTSIDE = ('engine', 'platforms')
IMPORT = re.compile(r'^import (\S+)', re.M)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()


def lines(text):
    return len(text.split('\n')) - text.endswith('\n')


def parent(path):
    return path.rsplit('/', 1)[0] if '/' in path else None


def plan(layout):
    tracked = git('ls-files').splitlines()
    text = {f: (REPO / f).read_text() for f in tracked if f.endswith('.lean') or f.startswith('app/')}
    app = [f for f in tracked if f.startswith('app/')]
    files = {}
    for f in app:
        if f.rsplit('/', 1)[1] not in ORDER:
            raise SystemExit(f'{f}: not one of the eight names')
        files[f] = {'text': text[f], 'lines': lines(text[f]), 'sha256': hashlib.sha256(text[f].encode()).hexdigest()}
    folders = set()
    for f in app:
        d = parent(f)
        while d:
            folders.add(d)
            d = parent(d)

    meta, notes = {}, []
    for n in layout['nodes']:
        p = n['path']
        if p == 'app' or p.startswith('app/'):
            meta[p] = n
        elif p.split('/')[0] in OUTSIDE and (p in OUTSIDE or any(f.startswith(p + '/') for f in tracked)):
            notes.append(n)
        else:
            raise SystemExit(f'{p}: in layout/tree.json but not a folder of app/, engine/ or platforms/')

    nodes = {}
    for p in sorted(folders | set(meta)):
        n = dict(meta.get(p, {'path': p}))
        if p not in folders and not n.get('planned'):
            raise SystemExit(f'{p}: in layout/tree.json but not on disk; fix its path or mark it planned')
        if p != 'app' and parent(p) not in folders | set(meta):
            raise SystemExit(f'{p}: its parent folder is neither on disk nor planned')
        n['name'] = p.split('/')[-1]
        n['parent'] = parent(p)
        nodes[p] = n
    for p, n in nodes.items():
        n['children'] = sorted((c for c in nodes if parent(c) == p), key=lambda c: nodes[c]['name'])
        has = {f.rsplit('/', 1)[1] for f in app if parent(f) == p}
        if 'Op.lean' in has:
            if n.get('planned'):
                raise SystemExit(f'{p}: an op on disk, still marked planned in layout/tree.json')
            n['kind'] = 'op'
            tags = re.findall(r'Codec Body := Codec\.tagged (\d+)', text[f'{p}/Op.lean'])
            if len(tags) == 1:
                n['tag'] = int(tags[0])
        elif n.get('planned'):
            n['kind'] = 'family' if n['planned'] == 'family' else 'op'
        elif n['children'] or p == 'app':
            n['kind'] = 'family'
        else:
            raise SystemExit(f'{p}: neither an op (Op.lean), a family (child folders) nor planned')
        names = set(has)
        if n['kind'] == 'op':
            names |= set(REQUIRED)
        if n.get('view'):
            names.add('View.lean')
        if n.get('screen'):
            names.add('Screen.lean')
        if n['children'] and n['parent'] == 'app':
            names.add('Family.lean')
        n['files'] = [f for f in ORDER if f in names]

    # The tests and shells that import a module of each folder today.
    users = {}
    for f in tracked:
        if f.endswith('.lean') and f.startswith(('tests/', 'platforms/')):
            for m in IMPORT.findall(text[f]):
                if m.startswith('app.'):
                    users.setdefault(m.rsplit('.', 1)[0].replace('.', '/'), set()).add(f)
    for p, n in nodes.items():
        n['tests'] = sorted(users.get(p, ()))[:12]

    def listing(root):
        return [{'path': f, 'lines': lines(text[f]),
                 'importsApp': [m for m in IMPORT.findall(text[f]) if m.startswith('app.')]}
                for f in tracked if f.startswith(root + '/') and f.endswith('.lean')]

    return {
        'revision': git('rev-parse', 'HEAD'), 'repository': 'holmesworcester/lean-quiet',
        'roles': layout['roles'], 'nodes': list(nodes.values()), 'notes': notes, 'files': files,
        'engine': listing('engine'), 'platforms': listing('platforms'),
    }


def tree_text(p):
    nodes = {n['path']: n for n in p['nodes']}
    out = ['app/']

    def visit(path, indent):
        n = nodes[path]
        entries = [(c, None) for c in n['children']] + [(None, f) for f in n['files']]
        for k, (c, f) in enumerate(entries):
            last = k == len(entries) - 1
            mark = '└── ' if last else '├── '
            if f:
                out.append(f'{indent}{mark}{f}{"" if f"{path}/{f}" in p["files"] else "   (planned)"}')
            else:
                kid = nodes[c]
                out.append(f'{indent}{mark}{kid["name"]}/{"   (planned " + kid["kind"] + ")" if kid.get("planned") else ""}')
                visit(c, indent + ('    ' if last else '│   '))
    visit('app', '')
    return ('Lean Quiet: the op tree\n'
            'Generated by tools/workspace/tools/plan.py from the files on disk under app/ and\n'
            'tools/workspace/layout/tree.json. (planned) marks a file LAYOUT02 requires that is\n'
            'not on disk yet; (planned op) and (planned family) mark folders that are not one yet.\n\n'
            + '\n'.join(out) + '\n')


def main(args):
    layout = Path(args[args.index('--layout') + 1]) if '--layout' in args else ROOT / 'layout/tree.json'
    p = plan(json.loads(layout.read_text()))
    if '--out' in args:
        Path(args[args.index('--out') + 1]).write_text(json.dumps(p, ensure_ascii=False))
    if '--write-tree' in args:
        Path(args[args.index('--write-tree') + 1]).write_text(tree_text(p))
    if '--check-tree' in args:
        path = Path(args[args.index('--check-tree') + 1])
        if not path.exists() or path.read_text() != tree_text(p):
            raise SystemExit(f'{path} is stale. Run mise run workspace:layout.')
    if not {'--out', '--write-tree', '--check-tree'} & set(args):
        print(tree_text(p), end='')


if __name__ == '__main__':
    main(sys.argv[1:])
