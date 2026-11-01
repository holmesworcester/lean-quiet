#!/usr/bin/env python3
"""Negative controls for Get started and the shell rule: each mutation of
the running code must be caught, by a law (`lake env lean` of its laws file
fails) or by the real desktop driver suite (`host:desktop` fails at the
named check). Every file is restored, even on failure."""
import os
import subprocess as sp
from pathlib import Path

app = Path(__file__).resolve().parents[2]
out = app / 'out/start-negative'
out.mkdir(parents=True, exist_ok=True)
env = {**os.environ, 'PATH': os.environ.get('ELAN_HOME', '/mnt/storage/elan') + '/bin:' + os.environ['PATH']}
layout = app / 'engine/renderer/desktop/Layout.lean'
pages = app / 'app/community/Screen.lean'
types = app / 'app/Screen.lean'

# (name, file, old, new, module to build, laws file that must fail | None, driver check that must fail | None)
mutations = [
    ('shell-ignored', layout, 'if !shell then ⟨w, ⟨0, 0⟩, ⟨0, w⟩, ⟨w, 0⟩⟩', 'if false then ⟨w, ⟨0, 0⟩, ⟨0, w⟩, ⟨w, 0⟩⟩',
     'engine.renderer.desktop.Layout', 'engine/renderer/desktop/ZoomLaws.lean', None),
    ('row-stride', pages, 'let top := g.card4 + 4 + 196 * i', 'let top := g.card4 + 4 + 200 * i',
     'app.Screen', 'app/Proofs.lean', None),
    ('off-centre', pages, '240 + (stage4 - 240 - startBody lines) / 2', '240 + (stage4 - 240 - startBody lines) / 3',
     'app.Screen', 'app/Proofs.lean', None),
    ('taps-not-rows', pages, '⟨startPaint f dm W h g caption rows, startTaps dm g rows⟩', '⟨startPaint f dm W h g caption rows, (startTaps dm g rows).reverse⟩',
     'app.Screen', 'app/Proofs.lean', None),
    ('member-always', types, 'def St.member (s : St) : Bool := s.comms.any (!·.waiting)', 'def St.member (s : St) : Bool := true',
     'desktop', None, 'Link devices opens its explanatory page full-window, not a drawer'),
]


def run(args, log, timeout=1200):
    p = sp.run(args, cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=timeout)
    log.write_text(p.stdout)
    return p


for name, path, old, new, module, laws, check in mutations:
    original = path.read_text()
    assert old in original, (name, 'mutation target missing')
    try:
        path.write_text(original.replace(old, new))
        built = run(['lake', 'build', module], out / f'{name}-build.log')
        assert built.returncode == 0, f'{name}: mutant does not build; {out}/{name}-build.log'
        if laws:
            p = run(['lake', 'env', 'lean', laws], out / f'{name}.log')
            assert p.returncode != 0 and 'error' in p.stdout and 'sorry' not in p.stdout, f'{name}: law did not catch it'
        if check:
            p = run(['.lake/build/bin/desktop', str(app / 'out' / f'start-negative-{name}')], out / f'{name}.log', timeout=900)
            assert p.returncode != 0 and f'FAIL {check}' in p.stdout, f'{name}: driver suite did not catch it'
        print('rejected', name, flush=True)
    finally:
        path.write_text(original)
run(['lake', 'build', 'desktop', 'app.Proofs', 'engine.renderer.desktop.ZoomLaws'], out / 'restored.log')
print('get started: 5 mutants rejected (shell rule, row stride, centring, taps, membership)')
