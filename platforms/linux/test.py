#!/usr/bin/env python3
"""Real X11 input, windows, resize and screenshots. Own and reap every PID."""
import os
from pathlib import Path
import subprocess as sp
import time
import socket
from PIL import Image

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT
OUT = APP / 'out/linux'
OUT.mkdir(parents=True, exist_ok=True)
checks = 0

# Fail clearly when the execution policy forbids Xvfb's local sockets.
# Otherwise Xvfb's display-number scan repeats the same denial 65536 times.
probe = OUT / f'socket-probe-{os.getpid()}'
try:
    with socket.socket(socket.AF_UNIX) as sock:
        sock.bind(str(probe))
finally:
    probe.unlink(missing_ok=True)


def check(ok, label):
    global checks
    assert ok, label
    checks += 1
    print('ok', label, flush=True)


def wait(fn, label, timeout=25):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        value = fn()
        if value:
            return value
        time.sleep(.05)
    raise AssertionError('timeout: ' + label)


read_fd, write_fd = os.pipe()
with (OUT / 'xvfb.log').open('w') as log:
    xvfb = sp.Popen(['Xvfb', '-displayfd', str(write_fd), '-screen', '0', '2400x1800x24', '-nolisten', 'tcp', '-ac'],
                    pass_fds=(write_fd,), stdout=log, stderr=log)
os.close(write_fd)
try:
    import select
    assert select.select([read_fd], [], [], 10)[0], 'Xvfb did not start'
    number = os.read(read_fd, 32).decode().strip()
    assert number.isdigit(), 'Xvfb cannot create a local display; see out/linux/xvfb.log'
    display = ':' + number
    os.close(read_fd)
    env = dict(os.environ, DISPLAY=display)

    def xdo(*args):
        return sp.check_output(['xdotool', *map(str, args)], env=env, text=True).strip()

    for scale, fallback in [(1, False), (2, False), (1, True)]:
        tag = f'{scale}x-' + ('putimage' if fallback else 'shm')
        state = OUT / (tag + '.state')
        db = OUT / (tag + '.db')
        for p in [state, db, Path(str(db)+'-wal'), Path(str(db)+'-shm')]:
            p.unlink(missing_ok=True)
        e = dict(env, QUIET_DB=str(db), QUIET_STATE=str(state), QUIET_SCALE=str(scale))
        if fallback:
            e['QUIET_NO_SHM'] = '1'
        with (OUT / (tag + '.log')).open('w') as log:
            proc = sp.Popen([str(APP / '.lake/build/bin/linux'), '--demo'], cwd=APP, env=e, stdout=log, stderr=log)
        try:
            def lines():
                try:
                    return state.read_text().splitlines()
                except FileNotFoundError:
                    return []

            wait(lambda: len(lines()) >= 8 and lines()[3] == 'App.PageId.chat', 'demo ready')
            win = xdo('search', '--onlyvisible', '--name', '^Lean Quiet$').splitlines()[-1]
            xdo('windowfocus', '--sync', win)

            def click(x, y):
                xdo('mousemove', '--window', win, x*scale, y*scale, 'click', '1')

            def shot(name):
                time.sleep(.2)
                path = OUT / f'{tag}-{name}.png'
                sp.run(['import', '-window', win, str(path)], env=env, check=True)
                return Image.open(path).convert('RGB')

            image = shot('chat')
            check(image.size == (1100*scale, 760*scale), tag + ' window size')
            check(image.getpixel((2*scale, 140*scale)) == (118,71,199), tag + ' Lean purple survives RGB/X11 blit')
            before = lines()[1]
            click(90, 28)
            click(90, 116)  # second accepted community, by its drawn row
            wait(lambda: len(lines()) >= 2 and lines()[1] != before, 'community switch')
            check(True, tag + ' community switched by X pointer')
            click(90, 730)
            wait(lambda: 'Desktop.Context.settings' in lines(), 'settings')
            image = shot('settings')
            check(image.getpixel((725*scale, 420*scale)) == (58,61,65), tag + ' context divider at 1100-375')
            xdo('windowsize', '--sync', win, 770*scale, 600*scale)
            wait(lambda: lines() and lines()[0] == '770 600', '770 resize')
            image = shot('770')
            check(image.getpixel((495*scale, 420*scale)) == (58,61,65), tag + ' context minimum at 770')
            xdo('windowsize', '--sync', win, 719*scale, 600*scale)
            wait(lambda: lines() and lines()[0] == '719 600', '719 resize')
            image = shot('719')
            check(image.getpixel((100*scale,420*scale)) == (38,41,46), tag + ' context replaces narrow window')
            click(695, 24)
            wait(lambda: 'Desktop.Context.closed' in lines(), 'close context')
            xdo('windowsize', '--sync', win, 1100*scale, 760*scale)
            wait(lambda: lines() and lines()[0] == '1100 760', 'restore size')
            click(300, 676)
            xdo('type', '--clearmodifiers', '--delay', '5', 'desktop input')
            wait(lambda: 'desktop input' in lines(), 'keyboard')
            check(True, tag + ' keyboard edits real composer')
            xdo('key', 'ctrl+a', 'ctrl+c', 'End', 'ctrl+v')
            wait(lambda: 'desktop inputdesktop input' in lines(), 'clipboard roundtrip')
            check(True, tag + ' UTF8 clipboard roundtrip')
            xdo('key', 'ctrl+a')
            xdo('type', '--clearmodifiers', 'hello world')
            wait(lambda: 'hello world' in lines(), 'replace selection')
            xdo('mousemove', '--window', win, 237*scale, 677*scale, 'mousedown', '1',
                'mousemove', '--window', win, 277*scale, 677*scale)
            time.sleep(.2)
            xdo('mouseup', '1')
            wait(lambda: any('#[0, 5,' in s for s in lines()), 'drag selection')
            check(True, tag + ' drag selects codepoints')
            shot('selection')
            xdo('key', 'Return')
            wait(lambda: len(lines()) >= 6 and lines()[4] == '' and int(lines()[5]) >= 1, 'send')
            check(True, tag + ' send reaches writer')
            # Exit through the WM protocol, never signal unrelated processes.
            xdo('windowclose', win)
            proc.wait(timeout=10)
            check(proc.returncode == 0, tag + ' window closes cleanly')
        finally:
            if proc.poll() is None:
                proc.terminate()
                proc.wait(timeout=10)
    print(f'linux: {checks} checks; 3 Xvfb sessions', flush=True)
finally:
    xvfb.terminate()
    xvfb.wait(timeout=10)
