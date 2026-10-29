#!/usr/bin/env python3
"""Mutate running code, require rejection, restore it in finally, rebuild.

Run with no other app build in progress. Every mutation must compile as
code before the law/test is allowed to reject it.
"""
import os
from pathlib import Path
import subprocess as sp

root = Path(__file__).resolve().parents[2]
app = root
env = dict(os.environ)
env['ELAN_HOME'] = env.get('ELAN_HOME', '/mnt/storage/elan')
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']
env['TMPDIR'] = env.get('TMPDIR', '/mnt/storage/holmes-tmp')
out = app / 'out/desktop/negative'
out.mkdir(parents=True, exist_ok=True)
layout = app / 'engine/renderer/desktop/Layout.lean'
original = layout.read_text()
mutations = [
    ('widths', 'w - 220⟩', 'w - 220 + 1⟩'),
    ('adjacent', '⟨220, w - 220⟩', '⟨221, w - 220⟩'),
    ('minimum', '⟨w - 375, 375⟩', '⟨w - 1, 1⟩'),
    ('monotone', 'if 720 ≤ w then', 'if 720 ≤ w && w < 2000 then'),
    ('controls_fit', 'xs.filter fun c => decide (Fits g h c.pane c.box)', 'xs.filter fun _ => true'),
    ('controls_screen', 'b.x + b.w ≤ (g.track p).x + (g.track p).w ∧', 'b.x + b.w ≤ (g.track p).x + (g.track p).w + 1 ∧'),
    ('hit_drawn', 'xs.find? fun c => c.box.has x y', '(xs.map fun c => { c with label := c.label ++ "!" }).find? fun c => c.box.has x y'),
    ('witness', 'decide (Fits g h c.pane c.box)', 'decide (Fits g h c.pane c.box) && g.width != 720'),
]


def run(args, path, ok):
    p = sp.run(args, cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=120)
    path.write_text(p.stdout)
    assert (p.returncode == 0) == ok, f'{args}: unexpected result; {path}'
    return p.stdout


try:
    for name, old, new in mutations:
        assert old in original
        layout.write_text(original.replace(old, new))
        run(['lake', 'build', 'engine.renderer.desktop.Layout'], out / (name + '-code.log'), True)
        log = run(['lake', 'env', 'lean', 'engine/renderer/desktop/Laws.lean'], out / (name + '.log'), False)
        assert 'error:' in log and 'sorry' not in log
        print('rejected', name, flush=True)
finally:
    layout.write_text(original)
    run(['lake', 'build', 'engine.renderer.desktop.Laws'], out / 'restored.log', True)

shell = root / 'platforms/linux/shell.c'
original_c = shell.read_text()
for name, old, new in [
    ('utf8-backspace', 'do p--; while (p && ((unsigned char)q.text[p] & 0xc0) == 0x80);', 'p--;'),
    ('rgb', 'dst[0]=src[2]; dst[1]=src[1]; dst[2]=src[0];', 'dst[0]=src[0]; dst[1]=src[1]; dst[2]=src[2];'),
]:
    try:
        assert old in original_c
        shell.write_text(original_c.replace(old, new))
        log = run(['bash', 'platforms/linux/input_test.sh'], out / (name + '.log'), False)
        assert 'Assertion' in log, log
        print('rejected', name, flush=True)
    finally:
        shell.write_text(original_c)
run(['bash', 'platforms/linux/input_test.sh'], out / 'input-restored.log', True)
print('negative controls: 8 law mutations + 2 native mutations rejected; sources restored')
