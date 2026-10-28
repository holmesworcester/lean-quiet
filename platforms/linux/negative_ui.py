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

for name, path, old, new, expected in [
    ('switch', driver, 'App.switchTo i;', 'App.switchTo 0;', 'switch to distinct community'),
    ('draft', driver, '{ s with text := "", sel := #[0, 0, 0, 0] }', '{ s with sel := #[0, 0, 0, 0] }', 'switch clears editor and old draft'),
    ('resize', driver, 'rows := {}, heights := {},', 'rows := s.rows, heights := s.heights,', 'resize repaints cached rows'),
    ('settle', driver, '  if (s.W, s.Hs) != d.settled then settleFrame d else return d\n', '  return d\n', 'no row shows a placeholder'),
    ('composer', view, '      b := b.fill g.main.x (h - 60) (g.main.x + g.main.w) h Row.bg\n', '', 'composer overlap'),
]:
    original = path.read_text()
    assert old in original
    try:
        path.write_text(original.replace(old, new))
        p = sp.run(['lake', 'build', 'desktop'], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=120)
        (out / (name+'-build.log')).write_text(p.stdout)
        assert p.returncode == 0, p.stdout
        directory = app / ('out/negative-' + name)
        p = sp.run(['.lake/build/bin/desktop', str(directory)], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=60)
        if name == 'composer':
            assert p.returncode == 0, p.stdout
            p = sp.run(['python3', 'platforms/linux/compare.py', str(directory)], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=60)
        (out / (name+'.log')).write_text(p.stdout)
        assert p.returncode != 0 and expected in p.stdout, p.stdout
        print('rejected', name, flush=True)
    finally:
        path.write_text(original)

p = sp.run(['lake', 'build', 'linux', 'desktop'], cwd=app, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=120)
(out / 'ui-restored.log').write_text(p.stdout)
assert p.returncode == 0, p.stdout
print('negative controls: 5 UI mutations rejected; sources restored and executables rebuilt')
