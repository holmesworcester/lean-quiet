#!/usr/bin/env python3
"""Negative controls of the actual renderer, restored even after failure.

Run with no builds in progress. Every mutant is compiled separately;
proof controls must be rejected by Lean, behavior controls must build
and fail the corpus/regression suite, and pixel controls must build and
fail the headless comparison. No git reset, checkout or network access.
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
os.chdir(ROOT)
os.environ['ELAN_HOME'] = '/mnt/storage/elan'
os.environ['PATH'] = '/mnt/storage/elan/bin:' + os.environ['PATH']
os.environ['TMPDIR'] = '/mnt/storage/holmes-tmp'
OUT = ROOT / 'out/bidi-negative'
OUT.mkdir(parents=True, exist_ok=True)
BASIC = 'engine/renderer/bidi/Basic.lean'
PAINT = 'engine/renderer/Paint.lean'

# A payload mutation for every preservation helper. The downstream
# permutation/run laws are checked by the same kernel build.
proofs = [
    ('w1-keeps', '(x, d\') :: w1 d\' t', 'w1 d\' t'),
    ('w23-keeps', '(x, d\') :: w23 next t', 'w23 next t'),
    ('w4-keeps', '(x, d\') :: w4 d t', 'w4 d t'),
    ('et-keeps', '(x, d\') :: et (d\' == .en) t', 'et (d\' == .en) t'),
    ('weak-keeps', '(et false (et false ws).reverse).reverse', '(et false (et false ws).reverse).reverse.tail'),
    ('runs-keeps', 'chars := x :: b.chars', 'chars := b.chars'),
    ('attach-keeps', '(b, vs.headD fallback) :: attach fallback bs vs.tail', 'attach fallback bs vs.tail'),
    ('reset-keeps', '((b, if yes then p else v) :: rest, yes)', '(rest, yes)'),
    ('leveled-keeps', '(neutrals rtl rtl ds (following rtl ds)))).1', '(neutrals rtl rtl ds (following rtl ds)))).1.tail'),
    ('reverseRuns-perm', '| [] => run\n', '| [] => []\n'),
    ('reorder-perm', 'reverseRuns 1 [] (reverseRuns 2 [] xs)', 'xs ++ xs'),
    ('display-perm', '.flatMap (fun b => b.1.chars)', '.flatMap (fun b => b.1.chars.tail)'),
    ('number-order', '.flatMap (fun b => b.1.chars)', '.flatMap (fun b => b.1.chars.reverse)'),
    ('EN-AN-witness-W4', 'let ws := w4 (base rtl) (w23 (base rtl) (w1 (base rtl) xs))',
     'let ws := w23 (base rtl) (w1 (base rtl) xs)'),
    ('EN-witness-W5', '(et false (et false ws).reverse).reverse', 'ws'),
]
behavior = [
    ('W1', 'if d == .nsm then prev else d', 'if d == .nsm then .on else d'),
    ('W2', 'd == .en && strong == .al', 'd == .en && strong == .on'),
    ('W3', 'else if d == .al then .r else d', 'else if d == .al then .l else d'),
    ('W4', 'let ws := w4 (base rtl) (w23 (base rtl) (w1 (base rtl) xs))',
     'let ws := w23 (base rtl) (w1 (base rtl) xs)'),
    ('W5', '(et false (et false ws).reverse).reverse', 'ws'),
    ('W6', 'd == .es || d == .et || d == .cs then .on', 'd == .es || d == .et || d == .cs then .en'),
    ('W7', 'd == .en && strong == .l', 'd == .en && strong == .on'),
    ('N1', 'd == .r || number d then some true', 'd == .r then some true else if number d then some false'),
    ('N2', 'if prev == next then prev else rtl', 'if prev == next then prev else !rtl'),
    ('I1-I2', 'if number d then 2 else', 'if number d then 1 else'),
    ('L1-original-class', 'b.original == .b || b.original == .s || (b.original == .ws && trailing)',
     'b.kind == .b || b.kind == .s || (b.kind == .ws && trailing)'),
    ('L2', 'reverseRuns 1 [] (reverseRuns 2 [] xs)', 'reverseRuns 1 [] xs'),
]


def command(args, log):
    with open(log, 'w') as f:
        result = subprocess.run(args, stdout=f, stderr=subprocess.STDOUT)
    return result.returncode


def mutant(name, file, old, new, kind):
    path = ROOT / file
    original = path.read_text()
    assert original.count(old) == 1, (name, original.count(old))
    stem = OUT / (kind + '-' + name)
    try:
        path.write_text(original.replace(old, new))
        target = {'proof': 'engine.renderer.TextLaws', 'behavior': 'bidi_check', 'pixels': 'bidi_host'}[kind]
        code = command(['lake', 'build', target], str(stem) + '-build.log')
        if kind == 'proof':
            assert code != 0, f'{name}: broken law unexpectedly proved'
            log = pathlib.Path(str(stem) + '-build.log').read_text()
            assert 'error:' in log and 'Killed' not in log and 'timeout' not in log, log
        else:
            assert code == 0, f'{name}: mutant failed to build; see {stem}-build.log'
            exe = 'bidi_check' if kind == 'behavior' else 'bidi_host'
            args = ['.lake/build/bin/' + exe]
            if kind == 'pixels': args.append('out/bidi-negative-host')
            code = command(args, str(stem) + '-test.log')
            assert code == 1, f'{name}: expected failing tests, got {code}'
            log = pathlib.Path(str(stem) + '-test.log').read_text()
            assert 'FAIL' in log, f'{name}: no failed assertion'
        print(f'caught {kind}: {name}', flush=True)
    finally:
        path.write_text(original)


which = set(sys.argv[1:] or ['proof', 'behavior', 'pixels'])
if 'proof' in which:
    for name, old, new in proofs: mutant(name, BASIC, old, new, 'proof')
if 'behavior' in which:
    for name, old, new in behavior: mutant(name, BASIC, old, new, 'behavior')
if 'pixels' in which:
    mutant('reverse-clock-edge-digits', PAINT,
           'b.glyph f g.c (x + g.x) y c bold',
           'b.glyph f (if g.c == 0x31 then 0x30 else if g.c == 0x30 then 0x31 else g.c) (x + g.x) y c bold',
           'pixels')
# Leave all artifacts built from restored sources, not a mutant.
assert command(['lake', 'build', 'engine.renderer.TextLaws', 'bidi_check', 'bidi_host'],
               OUT / 'restored-build.log') == 0
print('all selected negative controls caught; sources and builds restored', flush=True)
