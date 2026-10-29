"""Real desktop browser-style zoom: shortcuts, hit tests, reflow and restart.
Own all subprocesses; retain state/log/screenshots on failure.
"""
import os
from pathlib import Path
import select
import subprocess as sp
import time
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/zoom/native'
OUT.mkdir(parents=True, exist_ok=True)

def wait(fn, label):
    end = time.monotonic() + 40
    while time.monotonic() < end:
        value = fn()
        if value:
            return value
        time.sleep(.05)
    raise AssertionError('timeout: ' + label)

r, w = os.pipe()
with (OUT / 'xvfb.log').open('w') as log:
    xvfb = sp.Popen(['Xvfb', '-displayfd', str(w), '-screen', '0', '2800x2000x24', '-nolisten', 'tcp', '-ac'], pass_fds=(w,), stdout=log, stderr=log)
os.close(w)
try:
    assert select.select([r], [], [], 10)[0], 'Xvfb startup'
    display = ':' + os.read(r, 32).decode().strip()
    os.close(r)
    for scale, fallback in [(1, False), (2, False), (1, True)]:
        tag = f'{scale}x-' + ('putimage' if fallback else 'shm')
        state, db = OUT / f'{tag}.state', OUT / f'{tag}.db'
        state.unlink(missing_ok=True)
        for suffix in ['', '-wal', '-shm', '.zoom']:
            Path(str(db) + suffix).unlink(missing_ok=True)
        env = dict(os.environ, DISPLAY=display, QUIET_STATE=str(state), QUIET_DB=str(db), QUIET_SCALE=str(scale), QUIET_WIDTH='1280', QUIET_HEIGHT='900')
        if fallback:
            env['QUIET_NO_SHM'] = '1'
        def xdo(*args):
            return sp.check_output(['xdotool', *map(str, args)], env=env, text=True).strip()
        def lines():
            try: return state.read_text().splitlines()
            except FileNotFoundError: return []
        def info(key):
            return next((s.split()[1:] for s in lines() if s.startswith(key + ' ')), [])
        def ready():
            return len(lines()) > 8 and lines()[3] == 'App.PageId.chat'
        def key(k):
            xdo('key', '--clearmodifiers', k)
        def click(x, y):
            xdo('mousemove', '--window', win, round(x*scale), round(y*scale), 'click', '1')
        def shot(label):
            time.sleep(.3)
            path = OUT / f'{tag}-{label}.png'
            sp.run(['import', '-window', win, str(path)], env=env, check=True)
            return path
        log = (OUT / f'{tag}.log').open('w')
        proc = sp.Popen([str(ROOT / '.lake/build/bin/linux'), '--demo', '--scroll-fixture'], cwd=ROOT, env=env, stdout=log, stderr=log)
        try:
            wait(ready, 'demo chat')
            win = xdo('search', '--onlyvisible', '--name', '^Lean Quiet$').splitlines()[-1]
            xdo('windowfocus', '--sync', win)
            shot('100')
            # Composer is not focused. Ctrl+= and Ctrl+Shift+= both zoom.
            key('ctrl+equal'); wait(lambda: info('zoom')[:1] == ['110'], '110%')
            key('ctrl+plus'); wait(lambda: info('zoom')[:1] == ['125'], '125%')
            assert info('zoom')[2:5] == ['200', 'cell', '18'], info('zoom')
            shot('125')
            # Hit actual scaled sidebar settings, then its Appearance row.
            click(50*1.25, 900-24*1.25)
            wait(lambda: 'Desktop.Context.settings' in lines()[2], 'scaled settings click')
            appearance = wait(lambda: info('appearance'), 'scaled appearance action')
            click(*map(int, appearance)); wait(lambda: 'appearance' in ' '.join(info('drawer')), 'appearance drawer')
            shot('125-settings')
            for _ in range(3): key('ctrl+equal')
            wait(lambda: info('zoom')[0] == '200' and lines()[3] == 'App.PageId.appearance', 'drawer reflows into narrow page')
            key('ctrl+minus')
            wait(lambda: info('zoom')[0] == '175' and 'appearance' in ' '.join(info('drawer')) and lines()[3] == 'App.PageId.chat', 'drawer restored across breakpoint')
            key('ctrl+minus'); key('ctrl+minus')
            wait(lambda: info('zoom')[0] == '125', 'return to 125')
            key('Escape'); wait(lambda: 'you' in ' '.join(info('drawer')), 'back to settings')
            key('Escape'); wait(lambda: 'Desktop.Context.closed' in lines()[2], 'close drawer')
            # At 200%, CSS width is 640: sidebar collapses and content reflows.
            for level in [150, 175, 200]:
                key('ctrl+equal'); wait(lambda: info('zoom')[:1] == [str(level)], str(level))
            shot('200')
            # Native pointer selection/edit/send still reaches the composer.
            editor = wait(lambda: info('editor'), 'editor geometry')
            click(int(editor[0])+8, int(editor[1])+8)
            key('ctrl+a'); xdo('type', '--clearmodifiers', 'Zoom draft')
            wait(lambda: lines()[4] == 'Zoom draft', 'zoomed draft')
            for _ in range(20): key('ctrl+equal')
            assert info('zoom')[0] == '200', 'upper clamp'
            key('ctrl+0'); wait(lambda: info('zoom')[0] == '100', 'reset')
            assert lines()[4] == 'Zoom draft', 'zoom changed draft'
            for level in [90, 80, 75, 67, 50]:
                key('ctrl+minus'); wait(lambda: info('zoom')[0] == str(level), str(level))
            shot('50')
            for _ in range(5): key('ctrl+minus')
            assert info('zoom')[0] == '50', 'lower clamp'
            key('ctrl+0'); wait(lambda: info('zoom')[0] == '100', 'reset 2')
            for _ in range(6): key('ctrl+equal')
            wait(lambda: info('zoom')[0] == '200', 'zoom before resize')
            xdo('windowsize', win, 390*scale, 600*scale)
            wait(lambda: lines()[0] == '390 600', 'small window')
            assert info('zoom')[0] == '200' and int(info('zoom')[2]) <= 195, info('zoom')
            xdo('windowsize', win, 1280*scale, 900*scale)
            wait(lambda: lines()[0] == '1280 900' and info('zoom')[2] == '320', 'requested zoom restored after grow')
            key('ctrl+0'); wait(lambda: info('zoom')[0] == '100', 'reset after resize')
            key('ctrl+equal'); key('ctrl+equal'); wait(lambda: info('zoom')[0] == '125', 'saved zoom')
        finally:
            proc.terminate()
            try: proc.wait(timeout=10)
            except sp.TimeoutExpired: proc.kill(); proc.wait()
            log.close()
        assert Path(str(db)+'.zoom').read_text() == '125'
        state.unlink(missing_ok=True)
        with (OUT / f'{tag}-restart.log').open('w') as log:
            proc = sp.Popen([str(ROOT / '.lake/build/bin/linux'), '--offline'], cwd=ROOT, env=env, stdout=log, stderr=log)
            try:
                wait(lambda: info('zoom')[:1] == ['125'], 'restart persisted zoom')
            finally:
                proc.terminate()
                try: proc.wait(timeout=10)
                except sp.TimeoutExpired: proc.kill(); proc.wait()
        print('zoom native:', tag, 'PASS', flush=True)
    # A compact review artifact from the running app, not a mockup.
    shots = [(name, Image.open(OUT / f'1x-shm-{name}.png').convert('RGB')) for name in ['50', '100', '125', '200']]
    canvas = Image.new('RGB', (1280, 980), 'white')
    draw = ImageDraw.Draw(canvas)
    for i, (name, pic) in enumerate(shots):
        x, y = (i%2)*640, (i//2)*490
        draw.text((x+12,y+8), name+'% - real Linux client', fill='black')
        pic.thumbnail((640,450))
        canvas.paste(pic,(x,y+32))
    canvas.save(OUT / 'zoom-comparison.png')
finally:
    xvfb.terminate()
    try: xvfb.wait(timeout=10)
    except sp.TimeoutExpired: xvfb.kill(); xvfb.wait()
