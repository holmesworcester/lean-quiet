#!/usr/bin/env python3
"""Record the real offline demo app, including narrow/wide resize and appearance."""
import os
from pathlib import Path
import select
import subprocess as sp
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/demo'
OUT.mkdir(parents=True, exist_ok=True)
state = OUT / 'state'
db = OUT / 'quiet.db'
for path in [state, db, Path(str(db)+'-wal'), Path(str(db)+'-shm')]:
    path.unlink(missing_ok=True)
r, w = os.pipe()
with (OUT/'xvfb.log').open('w') as log:
    xvfb = sp.Popen(['Xvfb', '-displayfd', str(w), '-screen', '0', '1120x900x24', '-nolisten', 'tcp', '-ac'], pass_fds=(w,), stdout=log, stderr=log)
os.close(w)
app = recording = None
try:
    assert select.select([r], [], [], 10)[0], 'Xvfb did not start'
    display = ':' + os.read(r, 32).decode().strip()
    os.close(r)
    env = dict(os.environ, DISPLAY=display, QUIET_DB=str(db), QUIET_STATE=str(state), QUIET_SCALE='1')
    sp.run(['xsetroot', '-solid', '#dddddd'], env=env, check=True)
    with (OUT/'app.log').open('w') as log:
        app = sp.Popen([str(ROOT/'.lake/build/bin/linux'), '--demo'], cwd=ROOT, env=env, stdout=log, stderr=log)
    def lines():
        return state.read_text().splitlines() if state.exists() else []
    def wait(fn):
        deadline = time.monotonic()+30
        while time.monotonic() < deadline:
            if fn(): return
            if app.poll() is not None: raise RuntimeError('App exited; see out/demo/app.log')
            time.sleep(.05)
        raise RuntimeError('Demo state did not arrive; see out/demo/app.log')
    def xdo(*args):
        return sp.check_output(['xdotool', *map(str,args)], env=env, text=True).strip()
    wait(lambda: len(lines()) >= 8 and lines()[3] == 'App.PageId.chat' and int(lines()[5]) >= 2)
    win = xdo('search', '--onlyvisible', '--name', '^Lean Quiet$').splitlines()[-1]
    xdo('windowmove', win, 10, 10)
    xdo('windowfocus', '--sync', win)
    def shot(name):
        time.sleep(.3)
        sp.run(['import', '-window', win, str(OUT/(name+'.png'))], env=env, check=True)
    def resize(width, height):
        xdo('windowsize', '--sync', win, width, height)
        wait(lambda: lines()[0] == f'{width} {height}')
        time.sleep(1.2)
    def click(x, y):
        xdo('mousemove', '--window', win, x, y, 'click', '1')
    with (OUT/'recording.log').open('w') as log:
        recording = sp.Popen(['ffmpeg', '-y', '-f', 'x11grab', '-framerate', '15', '-video_size', '1120x900', '-i', display+'+0,0', '-c:v', 'libx264', '-preset', 'ultrafast', '-crf', '22', '-pix_fmt', 'yuv420p', str(OUT/'responsive.mp4')], stdin=sp.PIPE, stdout=log, stderr=log)
    time.sleep(1.3)
    shot('desktop')
    _, ex, ey, _ = next(s for s in lines() if s.startswith('editor ')).split()
    click(int(ex)+30, int(ey)+4)
    xdo('type', '--clearmodifiers', '--delay', '40', 'This draft stays while I resize.')
    wait(lambda: 'This draft stays while I resize.' in lines())
    resize(719, 760)
    resize(390, 844)
    shot('mobile')
    resize(720, 760)
    resize(1100, 760)
    click(90, 730)
    wait(lambda: 'Desktop.Context.settings' in lines())
    time.sleep(1)
    shot('three-panes')
    click(800, 328)
    wait(lambda: 'App.PageId.appearance' in lines())
    _, _, x, y = next(s for s in lines() if s.startswith('choice dark ')).split()
    click(int(x), int(y))
    wait(lambda: 'theme dark' in lines())
    time.sleep(1)
    click(90, 197)
    wait(lambda: 'App.PageId.chat' in lines())
    shot('dark-desktop')
    resize(390, 844)
    shot('dark-mobile')
    time.sleep(1)
    recording.communicate(b'q', timeout=15)
    assert recording.returncode == 0, 'Recording failed'
    xdo('windowclose', win)
    app.wait(timeout=15)
    assert app.returncode == 0, 'App did not close cleanly'
    print(f'Demo video: {OUT / "responsive.mp4"}')
    print('Actual X11 screenshots: desktop, mobile, three-panes, dark-desktop, dark-mobile')
finally:
    for proc in [recording, app, xvfb]:
        if proc and proc.poll() is None:
            proc.terminate()
            proc.wait(timeout=15)
