#!/usr/bin/env python3
"""The Linux shell's resize plumbing, broken two ways; each must fail the
e2e (platforms/linux/test.sh) on the check it is there for. The source is
restored after each, and the shell rebuilt."""
import os
from pathlib import Path
import subprocess as sp

root = Path(__file__).resolve().parents[2]
shell = root / 'platforms/linux/shell.c'
out = root / 'out/desktop/negative'
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.setdefault('ELAN_HOME', '/mnt/storage/elan')
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']

for name, edits, expected in [
    # the old window: a background pixel (0, black), and ForgetGravity
    ('gravity', [('XCB_BACK_PIXMAP_NONE, XCB_GRAVITY_NORTH_WEST,', 'q.screen->black_pixel, XCB_GRAVITY_BIT_FORGET,'),
                 ('XCB_CW_BACK_PIXMAP | XCB_CW_BIT_GRAVITY', 'XCB_CW_BACK_PIXEL | XCB_CW_BIT_GRAVITY')],
     "a resize keeps the frame shown, never the server's fill"),
    # a window manager's sync request answered never
    ('sync', [('xcb_sync_set_counter(q.c,q.counter,q.sync_value); ', '')],
     'the sync counter is set after the frame at the new size'),
]:
    original = shell.read_text()
    mutated = original
    for old, new in edits:
        assert mutated.count(old) == 1, (name, old)
        mutated = mutated.replace(old, new)
    try:
        shell.write_text(mutated)
        p = sp.run(['bash', 'platforms/linux/test.sh'], cwd=root, env=env, stdout=sp.PIPE, stderr=sp.STDOUT,
                   text=True, timeout=900)
        (out / (name + '-x11.log')).write_text(p.stdout)
        assert p.returncode != 0 and expected in p.stdout, f'{name}: not refused; see {out / (name + "-x11.log")}'
        print('rejected', name, flush=True)
    finally:
        shell.write_text(original)
p = sp.run(['bash', 'platforms/linux/build.sh'], cwd=root, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True,
           timeout=900)
assert p.returncode == 0, p.stdout
print('negative controls: 2 X11 mutations rejected; source restored and the shell rebuilt')
