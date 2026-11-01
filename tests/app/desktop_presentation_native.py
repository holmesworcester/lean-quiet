#!/usr/bin/env python3
"""Owned Xvfb, actual production shell and Driver; keep all failure logs."""
import os
from pathlib import Path
import select
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/desktop-presentation/native'
OUT.mkdir(parents=True, exist_ok=True)
r, w = os.pipe()
with (OUT / 'xvfb.log').open('w') as log:
    server = subprocess.Popen(['Xvfb', '-displayfd', str(w), '-screen', '0', '1600x1200x24',
                               '-nolisten', 'tcp', '-ac'], pass_fds=(w,), stdout=log, stderr=log)
os.close(w)
try:
    assert select.select([r], [], [], 10)[0], 'Xvfb startup timeout; see xvfb.log'
    number = os.read(r, 32).decode().strip()
    assert number.isdigit(), 'invalid Xvfb display'
    env = dict(os.environ, DISPLAY=':' + number, QUIET_WIDTH='1100', QUIET_HEIGHT='760', QUIET_SCALE='1')
    for mode in ['shm', 'put-image']:
        env['QUIET_NO_SHM'] = '1' if mode == 'put-image' else '0'
        # The production switch is presence based; omit it in the SHM case.
        if mode == 'shm': env.pop('QUIET_NO_SHM', None)
        with (OUT / (mode + '.log')).open('w') as log:
            p = subprocess.run([str(ROOT / '.lake/build/bin/desktop_native_presentation')],
                               cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=60)
        report = (OUT / (mode + '.log')).read_text()
        print(report, end='', flush=True)
        assert p.returncode == 0 and 'desktop-native-presentation: 28 passed, 0 failed' in report, mode
finally:
    os.close(r)
    server.terminate()
    try: server.wait(timeout=5)
    except subprocess.TimeoutExpired: server.kill(); server.wait()
