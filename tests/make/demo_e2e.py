#!/usr/bin/env python3
"""`make demo`, end to end, under Xvfb (1920 x 1080, no window manager), as
a judge runs it: `make demo` opens Alice's laptop and Bob's, and this test
does what the judge does, by X input (xdotool): Bob's name, Agree & Join;
Waiting to join and Approve in Alice's window. Then it types a message in
Alice's window and checks that it reaches Bob's:

  by the app's state: Bob's newest message (QUIET_STATE) is Alice's, and
  by the screen: the bottom of Bob's conversation is, pixel for pixel, the
  bottom of Alice's (the same message drawn), while before the message it
  was not (the screenshot check's own control).

Then Bob's 👍 on that message and his reply reach Alice, both windows
close, and `make demo` exits 0. A second run checks `make demo
ARGS=--auto` (the join done for the judge, Bob's hi on Alice's screen and
her ❤️ on his).

  tests/make/demo_e2e.py                    both runs
  tests/make/demo_e2e.py --control offline  the negative control: once Bob
      is in, his app restarts with --offline (no sockets); Alice's message
      must then not reach him, and this test must fail at that check
      (tests/make/demo_negative.sh asserts it does)

Needs: the built app (make install, or mise run linux:build), Xvfb,
xdotool, ImageMagick's import, Python's PIL and make. Artifacts in
out/make/demo-e2e/ (or DEMO_E2E_OUT): screenshots of each step, both apps'
logs and state, result.txt (timings). Every process started here is reaped.
"""
import json
import os
from pathlib import Path
import re
import select
import shutil
import socket
import subprocess as sp
import sys
import time

from PIL import Image, ImageChops

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/make'))
import demo  # noqa: E402

OUT = Path(os.environ.get('DEMO_E2E_OUT') or ROOT / 'out/make/demo-e2e')
control = sys.argv[sys.argv.index('--control') + 1] if '--control' in sys.argv else None
assert control in (None, 'offline'), control
checks = 0
results = []
procs = []


def check(ok, label):
    global checks
    if not ok:
        print('FAIL', label, flush=True)
        raise AssertionError(label)
    checks += 1
    print('ok  ', label, flush=True)


def step(label, fn, timeout=60, devices=()):
    """Wait for fn, as a check: its label is what failed if it never holds."""
    try:
        value = demo.wait(fn, label, timeout, devices)
    except (TimeoutError, RuntimeError) as e:
        print('FAIL', label, f'({e})', flush=True)
        raise AssertionError(label) from e
    check(True, label)
    return value


def timed(name, t0):
    results.append(f'{name}_seconds={time.monotonic() - t0:.1f}')


# emptied (in the clean room the folder itself is the judge's, its parent root's)
shutil.rmtree(OUT, ignore_errors=True)
OUT.mkdir(parents=True, exist_ok=True)
# Fail clearly when the sandbox forbids Xvfb's local socket.
probe = OUT / f'socket-probe-{os.getpid()}'
with socket.socket(socket.AF_UNIX) as s:
    s.bind(str(probe))
probe.unlink()

read_fd, write_fd = os.pipe()
with (OUT / 'xvfb.log').open('w') as log:
    xvfb = sp.Popen(['Xvfb', '-displayfd', str(write_fd), '-screen', '0', '1920x1080x24', '-nolisten', 'tcp', '-ac'],
                    pass_fds=(write_fd,), stdout=log, stderr=log)
procs.append(xvfb)
os.close(write_fd)


def shot(name, win='root'):
    path = OUT / f'{name}.png'
    sp.run(['import', '-window', win, str(path)], env=env, check=True)
    return Image.open(path).convert('RGB')


def band(device, image):
    """The bottom of a window's conversation, the newest message's lines:
    from 90 px above the composer's text to 20 px above it, without the
    sidebar and the scrollbar."""
    x, y = map(int, device.value('editor').split()[:2])
    return image.crop((x - 17, y - 90, image.width - 30, y - 20))


def gone(pid):
    """pid has exited (and make demo has reaped it, or it is a zombie)."""
    try:
        return Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[0] == 'Z'
    except FileNotFoundError:
        return True


def same(a, b):
    """The fraction of pixels two images share."""
    if a.size != b.size:
        return 0.0
    diff = ImageChops.difference(a, b).convert('L').point(lambda v: 255 if v else 0)
    return 1 - diff.histogram()[255] / (a.width * a.height)


def make_demo(args, devdir):
    e = dict(env, LQ_DEMO_DIR=str(devdir))
    log = (OUT / (devdir.name + '-make.log')).open('w')
    p = sp.Popen(['make', '--no-print-directory', 'demo', *([f'ARGS={args}'] if args else [])], cwd=ROOT, env=e,
                 stdout=log, stderr=sp.STDOUT, start_new_session=True)
    procs.append(p)
    return p


def close(x, devices, make, label):
    for d in devices:
        if win := x.find('^' + re.escape(d.title) + '$'):
            x.run('windowclose', win)
    try:
        code = make.wait(30)
    except sp.TimeoutExpired:
        code = None
    check(code == 0, f'{label}: both windows closed, make demo exits 0 (exit {code})')


def keep(devdir):
    for d in ('alice', 'bob'):
        for f in ('log', 'state', 'launch.json'):
            if (devdir / d / f).exists():
                shutil.copy(devdir / d / f, OUT / f'{devdir.name}-{d}-{f}')


try:
    # Read up to the newline: Xvfb writes the number, then the newline, and
    # dies ("Cannot write display number") if the pipe closed in between.
    number = b''
    while not number.endswith(b'\n'):
        assert select.select([read_fd], [], [], 10)[0], 'Xvfb did not start'
        chunk = os.read(read_fd, 32)
        assert chunk, 'Xvfb exited; see xvfb.log'
        number += chunk
    number = number.decode().strip()
    os.close(read_fd)
    assert number.isdigit(), 'Xvfb cannot open a display; see xvfb.log'
    env = dict(os.environ, DISPLAY=':' + number)
    x = demo.X(env)

    # 1. make demo, as a judge runs it
    devdir = OUT / 'guided'
    alice, bob = demo.Device('Alice', devdir / 'alice'), demo.Device('Bob', devdir / 'bob')
    t0 = time.monotonic()
    make = make_demo('', devdir)
    wa = step("Alice's window opens, titled", lambda: x.find("^Lean Quiet: Alice's laptop$"), 120)
    wb = step("Bob's window opens, titled", lambda: x.find("^Lean Quiet: Bob's laptop$"), 60)
    alice.proc = bob.proc = make  # alive while make demo runs
    step("Alice's laptop shows Add members, its invite", lambda: alice.page() == 'App.PageId.invite', 60)
    step("Bob's laptop opened Alice's link: Choose a name",
         lambda: bob.page() == 'App.PageId.name' and (bob.value('invite') or '').startswith('https://'), 60)
    timed('windows', t0)
    ga = x.run('getwindowgeometry', wa)
    gb = x.run('getwindowgeometry', wb)
    pos = lambda g: tuple(map(int, g.split('Position: ')[1].split()[0].split(',')))
    size = lambda g: tuple(map(int, g.split('Geometry: ')[1].split()[0].split('x')))
    (ax, ay), (bx, by), (aw, ah) = pos(ga), pos(gb), size(ga)
    check(ay == by and ax + aw <= bx and bx + size(gb)[0] <= 1920 and ay + ah <= 1080,
          f'side by side on 1920 x 1080: Alice at {ax},{ay}, Bob at {bx},{by}, each {aw} x {ah}')
    shot('1-start')
    # Bob: his name, Continue, Agree & Join
    t0 = time.monotonic()
    x.type(bob, 'Bob')
    step('Bob types his name', lambda: bob.value('field') == 'Bob', 30)
    x.click(bob, 'Pages.Act.continue_')
    step("Bob's Agree & join", lambda: bob.page() == 'App.PageId.agree', 30)
    x.click(bob, 'Pages.Act.agree')
    step('Bob waits to be let in', lambda: bob.page() == 'App.PageId.waiting', 30)
    step("Bob's request reaches Alice's node over TCP", lambda: alice.asking() == 1, 60)
    timed('request', t0)
    step("Alice's sidebar shows Waiting to join", lambda: alice.control('App.PageId.requests'), 30)
    shot('2-waiting-to-join')
    x.click(alice, 'App.PageId.requests')
    step("Alice's Waiting to join page", lambda: alice.page() == 'App.PageId.requests', 30)
    shot('3-requests')
    t0 = time.monotonic()
    x.click(alice, 'Pages.Act.approve 0')
    step('Bob is let in: Quiet, #general', lambda: demo.joined(bob), 60)
    step("Alice's history reaches Bob", lambda: ('Alice', 'Welcome to Lean Quiet.', False) in bob.rows(), 60)
    timed('admitted', t0)
    x.click(alice, 'App.PageId.chat')
    step("Alice back in #general", lambda: alice.page() == 'App.PageId.chat', 30)
    shot('4-joined')

    if control == 'offline':
        # Bob's laptop goes offline: his app again, on his database, without sockets
        launch = json.loads((bob.folder / 'launch.json').read_text())
        pid = int((bob.folder / 'pid').read_text())
        x.run('windowclose', wb)
        step("Bob's app closes", lambda: gone(pid), 30)
        bob.state.unlink()
        with (OUT / 'bob-offline.log').open('w') as log:
            offline = sp.Popen([launch['argv'][0], '--offline'], cwd=ROOT, env=dict(env, **launch['env']),
                               stdout=log, stderr=sp.STDOUT)
        procs.append(offline)
        bob.win = None
        step('Bob, offline, opens #general again', lambda: demo.joined(bob), 60)

    # 2. A message typed in Alice's window reaches Bob's
    message = "Hello Bob! This went from Alice's laptop to yours, no server."
    before = band(bob, shot('5-bob-before', x.window(bob)))
    t0 = time.monotonic()
    x.compose(alice, message)
    step("Alice's message is in her conversation, sent",
         lambda: alice.rows()[:1] == [('Alice', message, False)], 30)
    # Both checks run, and each says if it fails: the negative control
    # (no sockets on Bob's side) must fail both of them.
    failed = []
    try:
        step("Bob's state shows Alice's message (QUIET_STATE)",
             lambda: bob.rows()[:1] == [('Alice', message, False)], 20 if control else 30)
        timed('message_a_to_b', t0)
    except AssertionError as e:
        failed.append(str(e))
    # The state says what the app holds before its frame reaches the X
    # server, and a row can show its placeholder for a frame or two under
    # load: capture both windows again until they agree, or 15 s pass.
    end = time.monotonic() + 15
    while True:
        time.sleep(.5)
        after_a = band(alice, shot('6-alice', x.window(alice)))
        after_b = band(bob, shot('6-bob', x.window(bob)))
        if same(after_a, after_b) > 0.995 or time.monotonic() > end:
            break
    shot('6-both')
    for name, image in (('band-alice', after_a), ('band-bob', after_b), ('band-bob-before', before)):
        image.save(OUT / f'{name}.png')
    s_after, s_before = same(after_a, after_b), same(after_a, before)
    results.append(f'band_same_after={s_after:.4f} band_same_before={s_before:.4f}')
    check(s_before < 0.97, f"the screen check's control: Bob's screen before the message differs from Alice's "
                           f"({s_before:.1%} alike)")
    try:
        check(s_after > 0.995, f"Bob's screen shows Alice's message as Alice's does ({s_after:.1%} of pixels alike)")
    except AssertionError as e:
        failed.append(str(e))
    if failed:
        raise AssertionError('; '.join(failed))

    # 3. Bob's reaction to it reaches Alice...
    t0 = time.monotonic()
    x.react(bob, '👍')
    step("Bob reacts 👍 to Alice's message", lambda: bob.rows(True)[:1] == [('Alice', message, False, ('👍1*',))], 30)
    step("Bob's 👍 reaches Alice (her QUIET_STATE)", lambda: alice.rows(True)[:1] == [('Alice', message, False, ('👍1',))], 30)
    timed('reaction_b_to_a', t0)
    shot('7-reaction')

    # 4. ...and so does his reply
    reply = 'Got it! Hi Alice.'
    t0 = time.monotonic()
    x.compose(bob, reply)
    step("Bob's reply reaches Alice", lambda: alice.rows()[:1] == [('Bob', reply, False)], 30)
    timed('message_b_to_a', t0)
    shot('8-reply')
    close(x, [alice, bob], make, 'make demo')
    keep(devdir)

    # 5. make demo ARGS=--auto: the join done for the judge
    devdir = OUT / 'auto'
    alice, bob = demo.Device('Alice', devdir / 'alice'), demo.Device('Bob', devdir / 'bob')
    t0 = time.monotonic()
    make = make_demo('--auto', devdir)
    alice.proc = bob.proc = make
    step("make demo ARGS=--auto: Bob is in, his hi is on Alice's screen, and her ❤️ on his",
         lambda: demo.joined(bob) and ('Bob', "Hi Alice, it's Bob!", False, ('❤️1*',)) in alice.rows(True) and
         ('Bob', "Hi Alice, it's Bob!", False, ('❤️1',)) in bob.rows(True), 120, [alice])
    timed('auto', t0)
    time.sleep(1)
    shot('9-auto')
    close(x, [alice, bob], make, 'make demo ARGS=--auto')
    keep(devdir)
    print(f'demo e2e: {checks} checks pass; screenshots in {OUT}', flush=True)
    code = 0
except AssertionError as e:
    print(f'demo e2e FAILED: {e}; see {OUT}', flush=True)
    code = 1
except Exception as e:
    import traceback
    traceback.print_exc()
    print(f'demo e2e FAILED: {e!r}; see {OUT}', flush=True)
    code = 1
finally:
    for p in reversed(procs):
        if p.poll() is None:
            if p is not xvfb and p.args[0] == 'make':
                os.killpg(p.pid, 15)
            else:
                p.terminate()
            try:
                p.wait(15)
            except sp.TimeoutExpired:
                p.kill()
                p.wait()
    for d in ('guided', 'auto'):
        if (OUT / d).exists():
            keep(OUT / d)
    (OUT / 'result.txt').write_text('\n'.join(results + [f'checks={checks}', f'exit={code}']) + '\n')
sys.exit(code)
