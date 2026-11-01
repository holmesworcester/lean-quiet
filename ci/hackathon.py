#!/usr/bin/env python3
"""The numbers in docs/HACKATHON.md: what changed on main since the hackathon began.

The Vibecheck hackathon started on 2026-10-31 at 10:00 PDT, with main at
BASE. This script reads the base and a head with git alone (no build) and
writes the block between the hackathon markers in docs/HACKATHON.md. The
block names the commit it was computed at.

    python3 ci/hackathon.py              print the block for BASE..HEAD
    python3 ci/hackathon.py --write      write it into docs/HACKATHON.md
    python3 ci/hackathon.py --refresh    write it, commit the doc alone, then --self-test and --check
    python3 ci/hackathon.py --check      fail if HEAD's block is stale
    python3 ci/hackathon.py --self-test

Where each number comes from, at each revision:

- laws: README.md's lead line ("**N of M laws are about running code;**"),
  which ci/proof-links.py writes and the gate checks (`mise run readme:links`);
- README promises: the guarantee rows marked ✅, 🟡 or ⬜ (ci/proof-links.py
  checks that a ✅ row cites a law about running code);
- vacuity: README.md's "Coverage" line and its pending rows (ci/vacuity.py);
- caught bugs: docs/CAUGHT.md's entries, per section;
- code: commits, .lean files and lines, and `theorem` declarations.

A block computed at commit C is current for HEAD when C is HEAD or an
ancestor of it, nothing but docs/HACKATHON.md differs between them, and
the block is exactly what C gives. Run --refresh just before submission
(docs/RELEASE.md); --check is not in the per-push gate, since every
landing makes the block stale.
"""
import argparse
import datetime
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

TOP = Path(__file__).resolve().parents[1]
DOC = 'docs/HACKATHON.md'
BEGIN = '<!-- hackathon:begin -->'
END = '<!-- hackathon:end -->'
REPO = 'https://github.com/holmesworcester/lean-quiet'
# main at the start: 2026-10-31 10:00 PDT
BASE = '89914bea346ddf93d9a065a2e8bef0c79ed47797'
START = datetime.datetime(2026, 10, 31, 10, 0, tzinfo=datetime.timezone(datetime.timedelta(hours=-7)))
# A `theorem` declaration: at a line's start, after attributes and modifiers.
THEOREM = (r'^[[:space:]]*(@\[[^]]*\][[:space:]]*)*'
           r'((private|protected|noncomputable|nonrec)[[:space:]]+)*theorem[[:space:]]')


class Malformed(Exception):
    """A source this script reads does not have the shape it expects."""


class Stale(Exception):
    """The block does not hold for the head it is checked against."""


class Git:
    """git in this checkout, or in another git directory (the self-test's)."""

    def __init__(self, git_dir=None, env=None):
        self.cmd = ['git', '--git-dir', str(git_dir)] if git_dir else ['git', '-C', str(TOP)]
        self.env = env

    def __call__(self, *args, ok=(0,), input=None):
        env = dict(os.environ, **self.env) if self.env else None
        r = subprocess.run(self.cmd + list(args), capture_output=True, text=True,
                           encoding='utf-8', input=input, env=env)
        if r.returncode not in ok:
            raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
        return r.stdout

    def rev(self, rev):
        return self('rev-parse', '--verify', '--quiet', f'{rev}^{{commit}}').strip()

    def show(self, rev, path):
        """A file's text at a revision, or None where it does not exist."""
        return self('show', f'{rev}:{path}') if self.has(rev, path) else None

    def has(self, rev, path):
        return subprocess.run(self.cmd + ['cat-file', '-e', f'{rev}:{path}'],
                              capture_output=True).returncode == 0

    def ancestor(self, a, b):
        return subprocess.run(self.cmd + ['merge-base', '--is-ancestor', a, b],
                              capture_output=True).returncode == 0


# ---- the sources ----

LEAD_MARK = 'laws are about running code;**'
LEAD = re.compile(r'\*\*(\d+) of (\d+) laws are about running code;\*\* another (\d+) run its '
                  r'node code in a World, and (\d+) are not yet[.:]')


def parse_lead(readme):
    """README's lead line: laws about running code, in a World, not yet, proof steps, controls."""
    lines = [l for l in readme.splitlines() if LEAD_MARK in l]
    if len(lines) != 1:
        raise Malformed(f'README.md: expected one lead line ("**N of M {LEAD_MARK}"), found {len(lines)}')
    line = lines[0]
    m = LEAD.match(line)
    if not m:
        raise Malformed(f'README.md: the lead line does not read "**N of M laws are about running code;** '
                        f'another W run its node code in a World, and K are not yet": {line[:160]}')
    wired, total, world, not_yet = map(int, m.groups())
    if wired + world + not_yet != total:
        raise Malformed(f'README.md: the lead line\'s parts do not add up: {wired} + {world} + {not_yet} != {total}')
    controls = re.search(r'(?:^|\. )(\d+) laws are negative controls: ', line)
    if not controls:
        raise Malformed(f'README.md: the lead line names no count of negative controls: {line[:160]}')
    steps = re.search(r'(?:^|\. )(\d+) are proof steps: ', line)
    return {'wired': wired, 'total': total, 'world': world, 'not_yet': not_yet,
            'steps': int(steps.group(1)) if steps else None, 'controls': int(controls.group(1))}


ROW = re.compile(r'^\| (✅|🟡|⬜) \| 🥊+ \|(.*)$', re.M)
MARKS = ('✅', '🟡', '⬜')


def parse_rows(readme):
    """README's promises: the guarantee rows, by mark, and each row's bold title and mark."""
    rows = ROW.findall(readme)
    if not rows:
        raise Malformed('README.md: no guarantee rows ("| ✅ | 🥊🥊🥊 | **Title.** ...")')
    titles = {}
    for mark, rest in rows:
        m = re.match(r' \*\*(.+?)\*\*', rest)
        if not m:
            raise Malformed(f'README.md: a {mark} row has no bold title: {rest[:120]}')
        titles.setdefault(m.group(1).rstrip('.,:; '), mark)
    return {**{k: [r[0] for r in rows].count(k) for k in MARKS}, 'titles': titles}


def parse_vacuity(readme):
    """README's vacuity coverage, or None before the report existed."""
    i = readme.find('**Coverage:')
    if i < 0:
        return None
    j = readme.find('.**', i)
    text = ' '.join(readme[i:j].split()) if j > 0 else ''
    found = {}
    for key, pat in [('kernel', r'(\d+) kernel witnesses'), ('runtime', r'(\d+) runtime witnesses'),
                     ('conditional', r'(\d+) conditional checks'),
                     ('pending', r'(\d+) of \d+ linked declarations still pending'),
                     ('linked', r'\d+ of (\d+) linked declarations still pending')]:
        m = re.search(pat, text)
        if not m:
            raise Malformed(f'README.md: the vacuity coverage line has no "{pat}": {text[:200]}')
        found[key] = int(m.group(1))
    names = re.findall(r'^\| \[`([^`]+)`\]\([^)]*\) \| Pending: ', readme, re.M)
    if len(names) != found['pending']:
        raise Malformed(f'README.md: the coverage line says {found["pending"]} pending, '
                        f'the report lists {len(names)}')
    found['pending_names'] = names
    return found


def parse_caught(text):
    """docs/CAUGHT.md's entries per section: its ### entries, or else its top-level bold bullets."""
    if text is None:
        return None
    sections, cur = [], None
    for line in text.splitlines():
        if line.startswith('## '):
            cur = {'title': line[3:].strip(), 'heads': [], 'bullets': []}
            sections.append(cur)
        elif cur is None:
            continue
        elif line.startswith('### '):
            cur['heads'].append(line[4:].strip())
        elif line.startswith('- **'):
            cur['bullets'].append([line])
        elif cur['bullets'] and line.startswith('  '):
            cur['bullets'][-1].append(line)
    out = []
    for s in sections:
        if s['heads']:
            out.append({'title': s['title'], 'entries': s['heads'], 'test_only': None})
        elif s['bullets']:
            texts = [' '.join(' '.join(b).split()) for b in s['bullets']]
            titles = [re.match(r'- \*\*(.+?)\*\*', t).group(1) for t in texts]
            out.append({'title': s['title'], 'entries': titles,
                        'test_only': sum('not yet a law' in t for t in texts)})
    if not out:
        raise Malformed('docs/CAUGHT.md: no entries ("### ..." under a "## " section, or "- **...**")')
    return out


def lean_stats(git, rev):
    files = [p for p in git('ls-tree', '-r', '--name-only', rev).splitlines() if p.endswith('.lean')]

    def total(*args):
        out = git('grep', '-c', *args, rev, '--', '*.lean', ok=(0, 1))
        return sum(int(l.rsplit(':', 1)[1]) for l in out.splitlines())
    return {'files': len(files), 'lines': total(''), 'theorems': total('-E', THEOREM)}


def build_facts(git, rev):
    """What a judge's build reads at a revision: the Lean toolchain, the
    Makefile's .PHONY targets, the Comparator challenge, a LICENSE."""
    tc = git.show(rev, 'lean-toolchain')
    mk = git.show(rev, 'Makefile')
    targets = None
    if mk is not None:
        targets = []
        for l in mk.splitlines():
            if l.startswith('.PHONY:'):
                targets += [t for t in l.split(':', 1)[1].split() if t not in targets]
    cj = git.show(rev, 'comparator.json')
    comparator = None
    if cj is not None:
        try:
            d = json.loads(cj)
            comparator = {'theorems': len(d['theorem_names']), 'axioms': list(d.get('permitted_axioms', []))}
        except (ValueError, KeyError, TypeError) as e:
            raise Malformed(f'comparator.json at {rev[:12]}: {e}')
    return {'toolchain': tc.strip() if tc else None, 'make': targets, 'comparator': comparator,
            'license': git.has(rev, 'LICENSE')}


def history(git, base, head):
    """Commits in base..head, merges among them, and those authored before START."""
    commits = [l.split(' ') for l in git('log', '--format=%H %at %P', f'{base}..{head}').splitlines()]
    early = [c for c in commits if int(c[1]) < START.timestamp()]
    brought = {}
    for c in reversed(early):
        merge = None
        for m in git('rev-list', '--ancestry-path', '--merges', '--reverse', f'{c[0]}..{head}').split():
            if not git.ancestor(c[0], f'{m}^1'):
                merge = m
                break
        brought.setdefault(merge, []).append(c[0])
    stat = git('diff', '--shortstat', base, head)
    nums = {k: int(m.group(1)) if (m := re.search(rf'(\d+) {k}', stat)) else 0
            for k in ('file', 'insertion', 'deletion')}
    return {'commits': len(commits), 'merges': sum(len(c) > 3 for c in commits),
            'early': brought, 'early_days': sorted({day(git, c[0]) for c in early}), 'diff': nums}


def day(git, rev):
    return git('log', '-1', '--format=%ad', '--date=format:%Y-%m-%d', rev).strip()


def compute(git, base, head):
    base, head = git.rev(base), git.rev(head)
    if not base or not head:
        raise Malformed('base or head is not a commit')
    if not git.ancestor(base, head):
        raise Malformed(f'the base {base[:12]} is not an ancestor of {head[:12]}')
    side = {}
    for name, rev in (('base', base), ('head', head)):
        readme = git.show(rev, 'README.md')
        if readme is None:
            raise Malformed(f'{rev[:12]} has no README.md')
        side[name] = {'lead': parse_lead(readme), 'rows': parse_rows(readme),
                      'vacuity': parse_vacuity(readme),
                      'caught': parse_caught(git.show(rev, 'docs/CAUGHT.md')),
                      'lean': lean_stats(git, rev), 'build': build_facts(git, rev)}
    when = git('log', '-1', '--format=%cd', '--date=format:%Y-%m-%d %H:%M %z', head).strip()
    return {'base_rev': base, 'head_rev': head, 'when': when, **side, 'history': history(git, base, head)}


# ---- the block ----

def link(rev):
    return f'[`{rev[:12]}`]({REPO}/commit/{rev})'


def signed(n):
    return f'+{n:,}' if n > 0 else (f'-{-n:,}' if n < 0 else '0')


def render(s):
    b, h = s['base'], s['head']
    lb, lh = b['lead'], h['lead']
    pct = lambda l: round(100 * l['wired'] / l['total'])

    def row(label, x, y, show=lambda v: f'{v:,}'):
        if x is None and y is None:
            return []
        change = signed(y - x) if x is not None and y is not None else ''
        return [f'| {label} | {"—" if x is None else show(x)} | {"—" if y is None else show(y)} | {change} |']

    out = [BEGIN,
           f'Computed by `ci/hackathon.py` from git alone, at {link(s["head_rev"])} '
           f'(committed {s["when"]}), against the base {link(s["base_rev"])} '
           '(main at the start, 2026-10-31 10:00 PDT).', '',
           '| | Base | Head | Change |', '|---|--:|--:|--:|']
    out += row('Laws, as the README\'s lead counts them', lb['total'], lh['total'])
    out += [f'| … about running code | {lb["wired"]:,} ({pct(lb)}%) | {lh["wired"]:,} ({pct(lh)}%) '
            f'| {signed(lh["wired"] - lb["wired"])} |']
    out += row('… that run the node\'s code in a World', lb['world'], lh['world'])
    out += row('… not yet about running code', lb['not_yet'], lh['not_yet'])
    out += row('Proof steps (lemmas a law about running code uses; counted apart)', lb['steps'], lh['steps'])
    out += row('Negative controls (laws that prove a mutant breaks its law)', lb['controls'], lh['controls'])
    for mark, word in (('✅', 'proven over running code'), ('🟡', 'partly proven'), ('⬜', 'wanted, not proven')):
        out += row(f'README promises {word} ({mark})', b['rows'][mark], h['rows'][mark])
    out += row('`theorem` declarations in .lean files', b['lean']['theorems'], h['lean']['theorems'])
    out += row('.lean files', b['lean']['files'], h['lean']['files'])
    out += row('Lines of Lean', b['lean']['lines'], h['lean']['lines'])
    out.append('')
    tb, th = b['rows']['titles'], h['rows']['titles']
    moves = {}
    for title, mark in th.items():
        if title in tb and tb[title] != mark:
            moves.setdefault((tb[title], mark), []).append(title)
    order = [(x, y) for x in MARKS for y in MARKS]
    text = '; '.join(f'{x} → {y}: ' + ', '.join(f'"{t}"' for t in moves[(x, y)])
                     for x, y in order if (x, y) in moves) or 'none'
    fresh = sum(t not in tb for t in th)
    out.append(f'- **Promises that changed mark** (same title at the base and the head): {text}. '
               f'{fresh} promises at the head have a title the base does not have (new or reworded).')
    for name, side in (('the base', b), ('the head', h)):
        v = side['vacuity']
        if v is None:
            out.append(f'- **Vacuity** at {name}: no report (README.md has no "Vacuity check reports").')
            continue
        line = (f'- **Vacuity** at {name}: of {v["linked"]:,} declarations the README links, '
                f'{v["kernel"]:,} have a concrete input checked by Lean\'s kernel and {v["runtime"]:,} '
                f'one checked by running the code; {v["conditional"]:,} are conditional on a named '
                f'assumption; {v["pending"]:,} are pending')
        names = v['pending_names']
        out.append(line + (': ' + ', '.join(f'`{n}`' for n in names) + '.' if names else '.'))
    for name, side in (('the base', b), ('the head', h)):
        c = side['caught']
        if c is None:
            out.append(f'- **docs/CAUGHT.md** at {name}: absent.')
            continue
        parts = []
        for sec in c:
            n = len(sec['entries'])
            part = f'"{sec["title"]}": {n}'
            if sec['test_only'] is None:
                part += ' (' + '; '.join(sec['entries']) + ')'
            elif sec['test_only']:
                part += f', of which {sec["test_only"]} say they are pinned by a test, not yet a law'
            parts.append(part)
        out.append(f'- **docs/CAUGHT.md** at {name}: ' + '. '.join(parts) + '.')
    bb, bh = b['build'], h['build']
    tc = lambda t: t.split(':', 1)[-1] if t else 'none'
    out.append(f'- **Lean toolchain** (lean-toolchain): base {tc(bb["toolchain"])}; head {tc(bh["toolchain"])}.')
    for name, side in (('the base', bb), ('the head', bh)):
        mk, cj = side['make'], side['comparator']
        out.append(f'- **Build and judging files** at {name}: '
                   + (f'a Makefile with targets {", ".join(f"`{t}`" for t in mk)}' if mk is not None else 'no Makefile')
                   + '; ' + (f'comparator.json with {cj["theorems"]} theorems, permitted axioms '
                             + ', '.join(f'`{a}`' for a in cj['axioms']) if cj else 'no comparator.json')
                   + '; ' + ('a LICENSE file' if side['license'] else 'no LICENSE file') + '.')
    hist = s['history']
    early = hist['early']
    text = (f'- **Commits** since the base: {hist["commits"]:,}, of which {hist["merges"]:,} are merges. ')
    if early:
        n = sum(len(v) for v in early.values())
        groups = '; '.join(', '.join(f'`{c[:8]}`' for c in cs) + (f' (merged in `{m[:8]}`)' if m else '')
                           for m, cs in early.items())
        text += (f'{n} were authored before the start (on {", ".join(hist["early_days"])}): {groups}.')
    else:
        text += 'None was authored before the start.'
    out.append(text)
    d = hist['diff']
    out.append(f'- **Files changed** since the base: {d["file"]:,} '
               f'(+{d["insertion"]:,} lines, -{d["deletion"]:,} lines).')
    out.append(END)
    return '\n'.join(out)


def block_of(text):
    i, j = text.find(BEGIN), text.find(END)
    if i < 0 or j < i:
        raise Malformed(f'{DOC}: no block between "{BEGIN}" and "{END}"')
    return text[i:j + len(END)]


def check(git, head='HEAD'):
    """Raise Stale unless the block in head's docs/HACKATHON.md is current for head."""
    head = git.rev(head)
    doc = git.show(head, DOC)
    if doc is None:
        raise Stale(f'{head[:12]} has no {DOC}')
    block = block_of(doc)
    at = re.search(r'at \[`[0-9a-f]+`\]\(' + re.escape(REPO) + r'/commit/([0-9a-f]{40})\)', block)
    base = re.search(r'against the base \[`[0-9a-f]+`\]\(' + re.escape(REPO) + r'/commit/([0-9a-f]{40})\)', block)
    if not at or not base:
        raise Stale(f'{DOC}: the block names no commit it was computed at, or no base')
    at, base = at.group(1), base.group(1)
    if not git.rev(at) or not git.ancestor(at, head):
        raise Stale(f'{DOC}: computed at {at[:12]}, which is not {head[:12]} or an ancestor of it')
    changed = [p for p in git('diff', '--name-only', at, head).splitlines() if p != DOC]
    if changed:
        raise Stale(f'{DOC}: computed at {at[:12]}; since then {len(changed)} other files changed '
                    f'(e.g. {", ".join(changed[:3])}). Run: python3 ci/hackathon.py --refresh')
    want = render(compute(git, base, at))
    if block != want:
        diff = next((f'{x!r} != {y!r}' for x, y in zip(block.splitlines(), want.splitlines()) if x != y),
                    'the blocks differ in length')
        raise Stale(f'{DOC}: the block is not what {at[:12]} gives: {diff}')
    return at


def write(git, base, head):
    block = render(compute(git, base, head))
    path = TOP / DOC
    text = path.read_text(encoding='utf-8')
    old = block_of(text)
    path.write_text(text.replace(old, block), encoding='utf-8')
    dirty = [l[3:] for l in git('status', '--porcelain', '--untracked-files=no').splitlines() if l[3:] != DOC]
    if dirty:
        print(f'hackathon: note: uncommitted changes are not counted ({", ".join(dirty[:3])}...)',
              file=sys.stderr)
    return git.rev(head), old != block


# ---- the self-test ----

NO_MODELS_LEAD = (
    '**1159 of 1288 laws are about running code;** another 35 run its node code in a World, and 94 are '
    'not yet: `tests/wiring-models.txt` lists them, CI fails on any other law over a model, and the list '
    'only shrinks. Stated only: none. 59 are proof steps: lemmas that would be models, but that a law '
    'about running code uses in its proof (tests/Wiring.lean finds the use; a row citing one cites that '
    'law too). 25 laws are negative controls: each proves a mutant breaks its law (neither is counted '
    'here, nor in the lead).')

CAUGHT_SAMPLE = """# What the proofs caught

## Caught by a law

### One (2026-10-31)

- **Bug.** a
- **Fix.** b

### Two (found 2026-10-28; fix not on main)

## Found otherwise, pinned by a law afterwards

- **Three** happened. Pinned by a test, not yet
  a law: a test.
- **Four** happened, and a law pins it.
"""


def self_test():
    git = Git()
    failed = []

    def expect(name, ok):
        print(f"  {'ok  ' if ok else 'FAIL'} {name}")
        if not ok:
            failed.append(name)

    def refused(name, exc, f, *args):
        try:
            f(*args)
        except exc as e:
            print(f'  ok   {name}: refused ({e})'[:220])
            return
        except Exception as e:  # noqa: BLE001
            expect(f'{name}: refused with {exc.__name__}, not {type(e).__name__}: {e}', False)
            return
        expect(f'{name}: refused', False)

    base_readme = git.show(BASE, 'README.md')
    lead = parse_lead(base_readme)
    expect('the base reads 787 of 1016 laws about running code, 10 in a World, 219 not yet, 20 controls',
           lead == {'wired': 787, 'total': 1016, 'world': 10, 'not_yet': 219, 'steps': None, 'controls': 20})
    rows = parse_rows(base_readme)
    expect('the base has 40 ✅, 31 🟡 and 14 ⬜ promises, each with its own title',
           [rows[k] for k in MARKS] == [40, 31, 14] and len(rows['titles']) == 85
           and rows['titles'].get("A removal ends a live session's sync") == '🟡')
    refused('a promise row without a bold title', Malformed, parse_rows,
            base_readme.replace("| **A removal ends a live session's sync.**", '| A removal ends'))
    expect('the base has no vacuity report and no docs/CAUGHT.md',
           parse_vacuity(base_readme) is None and git.show(BASE, 'docs/CAUGHT.md') is None)
    expect('the lead line once tests/wiring-models.txt lands: 1159 of 1288, 59 proof steps, 25 controls',
           parse_lead(NO_MODELS_LEAD) == {'wired': 1159, 'total': 1288, 'world': 35, 'not_yet': 94,
                                          'steps': 59, 'controls': 25})

    bf = build_facts(git, BASE)
    expect('the base: Lean v4.34.0, no Makefile, no comparator.json, no LICENSE',
           bf == {'toolchain': 'leanprover/lean4:v4.34.0', 'make': None, 'comparator': None, 'license': False})
    # Negative controls: a malformed lead line fails loudly.
    line = next(l for l in base_readme.splitlines() if LEAD_MARK in l)
    for name, bad in [
            ('a lead line with a word for a number', line.replace('**787 of', '**seven hundred of')),
            ('a lead line whose parts do not add up', line.replace('of 1016 laws', 'of 1017 laws')),
            ('a lead line without its negative controls', line.split(' Stated only')[0]),
            ('a lead line reworded', line.replace('run its node code in a World', 'run in a World')),
            ('no lead line', ''),
            ('two lead lines', line + '\n' + line)]:
        refused(name, Malformed, parse_lead, base_readme.replace(line, bad))
    refused('a vacuity coverage line reworded', Malformed, parse_vacuity,
            '**Coverage: 3 kernel checks, 1 runtime witnesses, 0 conditional checks; 0 of 4 linked '
            'declarations still pending.**')
    refused('a vacuity report listing fewer pending rows than it counts', Malformed, parse_vacuity,
            '**Coverage: 3 kernel witnesses, 1 runtime witnesses, 0 conditional checks; 1 of 5 linked '
            'declarations still pending.**')
    refused('a docs/CAUGHT.md with no entries', Malformed, parse_caught, '# What the proofs caught\n\nNone.\n')
    caught = parse_caught(CAUGHT_SAMPLE)
    expect('docs/CAUGHT.md: ### entries in one section, bullets in the other, test-only ones counted',
           [(c['title'], c['entries'], c['test_only']) for c in caught] ==
           [('Caught by a law', ['One (2026-10-31)', 'Two (found 2026-10-28; fix not on main)'], None),
            ('Found otherwise, pinned by a law afterwards', ['Three', 'Four'], 1)])

    head = git.rev('HEAD')
    stats = compute(git, BASE, head)
    lh = stats['head']['lead']
    expect(f'HEAD reads: {lh["wired"]} of {lh["total"]} about running code, {lh["controls"]} controls',
           lh['controls'] >= 0 and lh['wired'] > 0)
    expect('the base side is the same computed from any head', stats['base']['lead'] == lead)
    expect('commits: base..HEAD counted', stats['history']['commits'] ==
           int(git('rev-list', '--count', f'{BASE}..{head}')))

    # --check: on commits made in a scratch git directory that borrows this
    # repository's objects, so no ref, index or file here changes.
    doc = git.show(head, DOC) or f'# x\n\n{BEGIN}\n{END}\n'
    old = block_of(doc)
    fresh = render(stats)
    tmp = Path(tempfile.mkdtemp(prefix='hackathon-', dir=os.environ.get('TMPDIR')))
    try:
        subprocess.run(['git', 'init', '-q', '--bare', str(tmp / 'r.git')], check=True)
        objects = Path(git('rev-parse', '--git-path', 'objects').strip())
        (tmp / 'r.git/objects/info/alternates').write_text(str(objects if objects.is_absolute() else TOP / objects) + '\n')
        who = {'GIT_AUTHOR_NAME': 'self-test', 'GIT_AUTHOR_EMAIL': 'self-test@invalid',
               'GIT_COMMITTER_NAME': 'self-test', 'GIT_COMMITTER_EMAIL': 'self-test@invalid',
               'GIT_INDEX_FILE': str(tmp / 'index')}
        t = Git(tmp / 'r.git', env=who)

        def commit(parent, files):
            t('read-tree', parent)
            for path, text in files.items():
                blob = t('hash-object', '-w', '--stdin', input=text).strip()
                t('update-index', '--add', '--cacheinfo', f'100644,{blob},{path}')
            return t('commit-tree', t('write-tree').strip(), '-p', parent, '-m', 'self-test').strip()

        refused('a block computed at the base, checked at HEAD', Stale, check, t, commit(
            head, {DOC: doc.replace(old, render(compute(git, BASE, BASE)))}))
        ok = commit(head, {DOC: doc.replace(old, fresh)})
        try:
            expect('a block computed at HEAD, committed alone: current', check(t, ok) == head)
        except (Stale, Malformed) as e:
            expect(f'a block computed at HEAD, committed alone: current ({e})', False)
        refused('the same, then README.md changed', Stale, check, t, commit(
            ok, {'README.md': git.show(head, 'README.md') + '\n'}))
        lines = fresh.splitlines()
        k = next(i for i, l in enumerate(lines) if l.startswith('| Lines of Lean'))
        lines[k] = re.sub(r'\| ([\d,]+) \| ([+\-\d,]+) \|$', r'| 1 | \2 |', lines[k])
        refused('a block computed at HEAD with one number edited', Stale, check, t, commit(
            head, {DOC: doc.replace(old, '\n'.join(lines))}))
        refused('a doc without the markers', Malformed, check, t, commit(head, {DOC: '# x\n'}))
    finally:
        subprocess.run(['rm', '-rf', str(tmp)], check=True)
    print('hackathon self-test: ' + ('ok' if not failed else f'{len(failed)} failed'))
    return not failed


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--base', default=BASE)
    p.add_argument('--head', default='HEAD')
    g = p.add_mutually_exclusive_group()
    g.add_argument('--write', action='store_true', help=f'write the block into {DOC}')
    g.add_argument('--refresh', action='store_true', help='--write, commit the doc alone, then --self-test and --check')
    g.add_argument('--check', action='store_true', help="fail if HEAD's block is stale")
    g.add_argument('--self-test', action='store_true')
    a = p.parse_args()
    git = Git()
    try:
        if a.self_test:
            return 0 if self_test() else 1
        if a.check:
            at = check(git, a.head)
            print(f'hackathon: {DOC} is current: computed at {at[:12]}, nothing else changed since')
            return 0
        if a.write or a.refresh:
            at, changed = write(git, a.base, a.head)
            print(f'hackathon: {DOC} computed at {at[:12]}' + ('' if changed else ' (unchanged)'))
            if a.refresh:
                if git('status', '--porcelain', '--', DOC).strip():
                    git('commit', '-q', '-m', f'HACKATHON.md: the numbers at {at[:12]}', '--', DOC)
                if not self_test():
                    return 1
                at = check(git)
                print(f'hackathon: {DOC} is current: computed at {at[:12]}')
            return 0
        print(render(compute(git, a.base, a.head)))
        return 0
    except Stale as e:
        print(f'hackathon: stale: {e}', file=sys.stderr)
        return 1
    except Malformed as e:
        print(f'hackathon: malformed: {e}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
