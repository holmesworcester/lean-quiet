"""ci/proof-tree.py on a small graph: shared subtrees drawn once, the depth
cap, the grouping by README group and folder, the scoreboard, and the
check's negative control (a stale or tampered doc fails it)."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('proof_tree', ROOT / 'ci/proof-tree.py')
tree = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tree)

X, Y, M = 'engine.core.X', 'engine.sync.Y', 'app.community.member.Proofs'
CHAIN = [f'C.n{i}' for i in range(1, 9)]  # C.h → C.n1 → … → C.n8, longer than DEPTH


def law(name, cls, module, uses=(), **more):
    return dict(name=name, **{'class': cls}, module=module, line=7, uses=list(uses), **more)


LAWS = [
    law('A.top1', 'wired', X, ['A.shared', 'A.c1']),
    law('A.top2', 'model', Y, ['A.shared']),
    law('A.shared', 'lemma', X, ['A.leaf1', 'A.mid']),
    law('A.mid', 'lemma', X, ['A.leaf1']),
    law('A.leaf1', 'lemma', X),
    law('A.c1', 'step', X, users=['A.top1']),
    law('C.h', 'wired', 'app.community.Proofs', ['C.n1']),
    *[law(n, 'lemma', 'app.community.Proofs', [CHAIN[i + 1]] if i + 1 < len(CHAIN) else [])
      for i, n in enumerate(CHAIN)],
    law('R.root1', 'wired', M, ['A.leaf1']),
    law('R.iso', 'model', M),
    law('P.prose', 'world', X, ['A.mid']),
]

README = """# Fixture

## What is proven

### Security proofs

| | | Guarantee | Theorems |
|---|---|---|---|
| | | **Group one** | |
| ✅ | 🥊 | **One.** | [`top1`], [`top2`] |
| | | **Group two** | |
| 🟡 | 🥊 | **Two.** Not yet. | [`C.h`] |

### Elsewhere

Prose cites [`prose`].

<!-- wiring:begin -->
| x | [`root1`] |
<!-- wiring:end -->
"""

ONE, TWO = 'proof-tree/security-proofs-group-one.md', 'proof-tree/security-proofs-group-two.md'


def nesting(text):
    """The deepest <details> nesting in a text."""
    deep = most = 0
    for tag in re.findall(r'</?details>', text):
        deep += 1 if tag == '<details>' else -1
        most = max(most, deep)
    return most


class ProofTreeTest(unittest.TestCase):
    def setUp(self):
        self.g = tree.Graph(LAWS)
        self.pages = tree.render(self.g, README)

    def test_files_follow_the_readme_groups(self):
        self.assertEqual(sorted(self.pages), sorted([tree.INDEX, ONE, TWO, tree.ALSO]))
        self.assertIn('id="law-A.top1"', self.pages[ONE])
        self.assertIn('id="law-A.top2"', self.pages[ONE])
        self.assertIn('id="law-C.h"', self.pages[TWO])
        self.assertIn('id="law-P.prose"', self.pages[tree.ALSO])
        # a generated block's citation is not one: root1 stays an uncited root
        self.assertNotIn('law-R.root1', ''.join(self.pages.values()))

    def test_shared_subtree_drawn_once(self):
        whole = ''.join(self.pages.values())
        self.assertEqual(whole.count('id="law-A.shared"'), 1)
        self.assertEqual(whole.count('id="law-A.mid"'), 1)
        # met again under top2, it links back; from another file, across
        self.assertIn('<a href="#law-A.shared">A.shared</a> ↪', self.pages[ONE])
        self.assertIn('href="security-proofs-group-one.md#law-A.mid"', self.pages[tree.ALSO])
        # a leaf is the same everywhere: its source, no anchor
        self.assertEqual(whole.count('id="law-A.leaf1"'), 0)
        self.assertGreater(whole.count('>A.leaf1</a>'), 1)

    def test_depth_cap(self):
        page = self.pages[TWO]
        top, deeper = page.split('## Deeper')
        self.assertLessEqual(nesting(top), tree.DEPTH)
        cut = CHAIN[tree.DEPTH - 1]  # met DEPTH levels down
        self.assertIn(f'<a href="#law-{cut}">{cut}</a> ↪', top)
        self.assertNotIn(f'id="law-{cut}"', top)
        self.assertIn(f'id="law-{cut}"', deeper)
        for n in CHAIN[:-1]:  # every law with a subtree is drawn whole once
            self.assertEqual(page.count(f'id="law-{n}"'), 1, n)

    def test_uncited_roots_by_folder(self):
        index = self.pages[tree.INDEX]
        self.assertIn('| app/community/member | 2 | 2 | 1 |', index)
        self.assertIn('Laws no law uses and the README does not cite: 2, 1 of them isolated', index)
        tail = index.split('## Uncited roots')[1]
        self.assertIn('>R.iso</a> · isolated', tail)
        self.assertIn('>R.root1</a> · 1 below', tail)
        for cited in ['A.top1', 'A.top2', 'C.h', 'P.prose']:
            self.assertNotIn(f'>{cited}</a>', tail)

    def test_metrics(self):
        rows, prose = tree.citations(README, self.g)
        self.assertEqual(rows, [('Security proofs › Group one', ['A.top1', 'A.top2']),
                                ('Security proofs › Group two', ['C.h'])])
        self.assertEqual(prose, [('Elsewhere', ['P.prose'])])
        cited = ['A.top1', 'A.top2', 'C.h']
        self.assertEqual(dict(tree.metrics(self.g, cited)), {
            'Laws': '18', 'Edges (a proof uses a law)': '16',
            'Roots (no law uses them)': '6 (33.3%)', 'Isolated (roots that use no law)': '1 (5.6%)',
            'Deepest chain': '8', 'Median chain': '2',
            "Headlines (laws the README's guarantee rows cite)": '3',
            'Laws the headlines build on, or are': '15 (83.3%)'})
        for k, v in tree.metrics(self.g, cited):
            self.assertIn(f'| {k} | {v} |', self.pages[tree.INDEX])

    def test_step_shows_its_wired_users(self):
        self.assertIn('🪜 <a href="../../engine/core/X.lean#L7">A.c1</a> · a step of A.top1</li>', self.pages[ONE])

    def test_unknown_class_fails(self):
        with self.assertRaisesRegex(ValueError, "unknown class 'stepping' of A.x"):
            tree.Graph([law('A.x', 'stepping', X)])
        with self.assertRaisesRegex(ValueError, 'A.x uses A.gone'):
            tree.Graph([law('A.x', 'lemma', X, ['A.gone'])])

    def test_check_fails_when_stale_or_tampered(self):
        with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as tmp:
            graph, readme, docs = (os.path.join(tmp, f) for f in ('graph.json', 'README.md', 'docs'))
            os.makedirs(docs)
            Path(graph).write_text(json.dumps({'laws': LAWS}))
            Path(readme).write_text(README)
            run = lambda *a: tree.main(['--graph', graph, '--readme', readme, '--docs', docs, *a])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(run(), 0)
                self.assertEqual(run('--check'), 0)
                # tampered: a count edited by hand
                page = Path(docs, ONE)
                good = page.read_text()
                page.write_text(good.replace('· 4 below', '· 5 below', 1))
                self.assertNotEqual(page.read_text(), good)
                self.assertEqual(run('--check'), 1)
                page.write_text(good)
                # stale: a law's proof uses one law less
                laws = [dict(l, uses=[]) if l['name'] == 'A.mid' else l for l in LAWS]
                Path(graph).write_text(json.dumps({'laws': laws}))
                self.assertEqual(run('--check'), 1)
                Path(graph).write_text(json.dumps({'laws': LAWS}))
                # a file left over, or one gone
                Path(docs, 'proof-tree', 'old.md').write_text('old\n')
                self.assertEqual(run('--check'), 1)
                os.remove(Path(docs, 'proof-tree', 'old.md'))
                os.remove(Path(docs, TWO))
                self.assertEqual(run('--check'), 1)
                self.assertEqual(run(), 0)
                self.assertEqual(run('--check'), 0)
            self.assertIn('stale: docs/proof-tree/security-proofs-group-one.md', out.getvalue())
            self.assertIn('negative control (one edge less) caught', out.getvalue())

    def test_negative_control(self):
        self.assertTrue(tree.control(self.g, README, self.pages))


if __name__ == '__main__':
    unittest.main()
