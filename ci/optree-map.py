#!/usr/bin/env python3
# Regenerate: python3 ci/optree-map.py <main before the cutover> > ci/optree-map.tsv
"""ci/optree-map.tsv: each Lean file the op-tree cutover moved, split or
merged (from BASE), and the files its declarations are in now (by count)."""
import re, subprocess, sys, collections
BASE = sys.argv[1]
git = lambda *a: subprocess.check_output(['git', *a], text=True)
old = [l.split('\t') for l in git('diff', '--name-status', '--no-renames', BASE, 'HEAD', '--', '*.lean').splitlines()]
gone = [p for st, p in old if st == 'D']
now = git('ls-files', '*.lean').split()
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |partial |unsafe )*'
                  r'(?:theorem|def|abbrev|structure|inductive|instance|class|lemma)\s+([^\s:({\[]+)', re.M)
def decls(text):
    out, ns = [], []
    for l in text.split('\n'):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        if re.match(r'^end\s+\S', l) and ns:
            if l.split()[1] == ns[-1]: ns.pop()
            continue
        m = DECL.match(l)
        if m: out.append('.'.join(ns + [m.group(1)]))
    return out
where = collections.defaultdict(set)
for f in now:
    if f.startswith(('app/', 'engine/')):
        for d in decls(open(f).read()): where[d].add(f)
rows = []
# umbrellas, and files whose namespace changed with their move
FIXED = {'ops/community/Community.lean': 'app/community/Proofs.lean (the umbrella: it imports its subtree)',
         'ops/connection/All.lean': 'app/connection/Proofs.lean (the umbrella: it imports its subtree; the root\'s commands and laws are app/Commands, app/Proofs)',
         'ops/community/Merkle.lean': 'engine/core/Merkle.lean (namespace Merkle, was Community.Merkle)',
         'ops/community/MerkleCost.lean': 'engine/core/MerkleCost.lean (namespace Merkle, was Community.Merkle)',
         'ops/connection/bootstrap/Net.lean': 'app/community/Proofs.lean (the bootstrap model is a section of it)'}
for p in sorted(gone):
    ds = decls(git('show', f'{BASE}:{p}'))
    c = collections.Counter()
    for d in ds:
        hs = where.get(d, set())
        for h in hs: c[h] += 1
    rows.append((p, FIXED.get(p) or ' '.join(h for h, _ in c.most_common()) or '(rewritten: see the op folders)'))
print('# The op-tree cutover (from main ' + BASE + '): each Lean file it removed, and where its')
print('# declarations are now, most first. Module names are paths: app/x/Y.lean is app.x.Y.')
print('old_path\tnew_paths')
for p, n in rows: print(f'{p}\t{n}')
