#!/usr/bin/env python3
"""Negative controls for dispatch, resize, draft isolation and composer overlap."""
import os
from pathlib import Path
import subprocess as sp

root = Path(__file__).resolve().parents[2]
app = root
env = dict(os.environ, ELAN_HOME='/mnt/storage/elan', TMPDIR='/mnt/storage/holmes-tmp')
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']
out = app / 'out/desktop/negative'
out.mkdir(parents=True, exist_ok=True)
driver = app / 'platforms/desktop/Driver.lean'
view = app / 'platforms/desktop/View.lean'

composer = app / 'app/community/channel/message/draft/View.lean'
life = app / 'app/Screen.lean'
for name, path, old, new, expected in [
    ('switch', driver, 'App.switchTo i;', 'App.switchTo 0;', 'switch to distinct community'),
    ('draft', driver, 'app := s, ui := { d.ui with switching := false }', 'app := { s with text := "" }, ui := { d.ui with switching := false }', 'returning to community restores its draft'),
    ('resize', life, 'if w == s.W && h == s.Hs && it == s.insetTop && ib == s.insetBot && dpi == s.dim.dpi then return', 'if true then return', 'every content pixel matches the shared mobile frame'),
    ('settle', driver, '  let d ← if (d.app.W, d.app.Hs) != d.settled then settleFrame d else pure d\n', '  let d ← pure d\n', 'no row shows a placeholder'),
    ('mobile', view, 'g.main.x 0 0', 'g.main.x 40 0', 'every content pixel matches the shared mobile frame'),
    ('composer', composer, 'min (px (if wide then 32 else 44)) ((W - 2 * gutter - px 16) / (acts.size + 1))', 'px 80', 'shared composer buttons fit without overlap'),
]:
    original = path.read_text()
    assert old in original, f'{name}: mutation anchor missing'
    try:
        path.write_text(original.replace(old, new))
        p = sp.run(['lake', 'build', 'desktop'], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=900)
        (out / (name+'-build.log')).write_text(p.stdout)
        assert p.returncode == 0, p.stdout
        directory = app / ('out/negative-' + name)
        p = sp.run(['.lake/build/bin/desktop', str(directory)], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=300)
        (out / (name+'.log')).write_text(p.stdout)
        assert p.returncode > 0 and 'PANIC' not in p.stdout and 'uncaught exception' not in p.stdout, p.stdout
        assert any(line.startswith('FAIL ') and expected in line
                   for line in p.stdout.splitlines()), f'{name}: intended assertion did not fail\n{p.stdout}'
        print('rejected', name, flush=True)
    finally:
        path.write_text(original)

p = sp.run(['lake', 'build', 'linux', 'desktop'], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=900)
(out / 'ui-restored.log').write_text(p.stdout)
assert p.returncode == 0, p.stdout
p = sp.run(['.lake/build/bin/desktop', str(app / 'out/desktop/restored')],
           cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=300)
(out / 'ui-restored-run.log').write_text(p.stdout)
assert p.returncode == 0, p.stdout
print('negative controls: 6 UI mutations rejected; restored desktop suite passes')
