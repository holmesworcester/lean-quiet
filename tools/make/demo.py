#!/usr/bin/env python3
"""`make demo`: two Lean Quiet apps side by side on this computer, as two
devices. Each has its own database and its own node, and they talk over
TCP on this machine (127.0.0.1), end-to-end encrypted, with no server.

  Alice's laptop (left) has a community, Quiet, with some history, and
  shows its invite (Add members). Bob's laptop (right) opens that link
  as a new device: it asks for Bob's name, then to agree and join. Alice's
  window then shows Waiting to join; approving Bob there lets him in, and
  Alice's history arrives on his screen. From then on, what either types
  shows in the other window.

  tools/make/demo.py           you do the join: Bob's name, Agree & Join,
                               then Approve in Alice's window
  tools/make/demo.py --auto    the join is done for you, as you would do it
                               (X input; needs xdotool), then Bob says hi

Each run starts afresh in out/make/demo/: alice/ and bob/ each hold a
database, a log and a state file (QUIET_STATE). Close both windows, or press
Ctrl-C here, to stop. Run by `make demo` (ARGS passes --auto); the e2e test
(tests/make/demo_e2e.py) imports it.
"""
import ctypes
import json
import os
from pathlib import Path
import re
import shutil
import signal
import socket
import subprocess as sp
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / '.lake/build/bin/linux'
# LQ_DEMO_DIR: another folder (tests/make/demo_e2e.py keeps its runs apart)
OUT = Path(os.environ.get('LQ_DEMO_DIR') or ROOT / 'out/make/demo')


def say(text):
    print('==> ' + text, flush=True)


class Device:
    """One app: its folder, process, window and the state it reports."""

    def __init__(self, name, folder):
        self.name = name
        self.folder = folder
        self.db = folder / 'quiet.db'
        self.state = folder / 'state'
        self.title = f"Lean Quiet: {name}'s laptop"
        self.proc = None
        self.win = None

    def lines(self):
        try:
            return self.state.read_text().splitlines()
        except FileNotFoundError:
            return []

    def page(self):
        ls = self.lines()
        return ls[3] if len(ls) > 3 else ''

    def community(self):
        ls = self.lines()
        return ls[1] if len(ls) > 1 else ''

    def value(self, key):
        """The rest of the first line `key ...` of the state."""
        return next((s[len(key) + 1:] for s in self.lines() if s.startswith(key + ' ')), None)

    def asking(self):
        v = self.value('asking')
        return int(v.split()[0]) if v else 0

    def waiting(self):
        v = self.value('asking')
        return v is not None and v.split()[2] == '1'

    def rows(self, tallies=False):
        """The newest messages it has mounted, newest first: (author, text,
        pending), and with `tallies` their reactions too (as 👍1, or 👍1*
        when one is this device's)."""
        out = []
        for s in self.lines():
            m = re.match(r'row "((?:[^"\\]|\\.)*)" "((?:[^"\\]|\\.)*)"(.*)$', s)
            if m:
                rest = m.group(3).split()
                row = (unquote(m.group(1)), unquote(m.group(2)), 'pending' in rest)
                out.append(row + (tuple(t for t in rest if t != 'pending'),) if tallies else row)
        return out

    def control(self, key):
        """The window-relative centre of a control the state lists: a page's
        button (`action <key> x y`), a sidebar page (`goto <key> x y`), a
        quick reaction (`quick <emoji> x y`) or the pointed-at message's Add
        a reaction (`react x y`)."""
        pattern = re.compile(r'^(?:(?:action|goto|quick) )?' + re.escape(key) + r' (\d+) (\d+)$')
        for s in self.lines():
            if m := pattern.match(s):
                return int(m.group(1)), int(m.group(2))
        return None

    def alive(self):
        return self.proc is not None and self.proc.poll() is None


def unquote(text):
    """A Lean string literal's body (its `repr`), unescaped."""
    return re.sub(r'\\(x[0-9a-fA-F]{2}|.)', lambda m: {'n': '\n', 't': '\t'}.get(m.group(1), m.group(1))
                  if not m.group(1).startswith('x') else chr(int(m.group(1)[1:], 16)), text)


def wait(fn, label, timeout=60, devices=()):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        value = fn()
        if value:
            return value
        for d in devices:
            if not d.alive():
                raise RuntimeError(f"{d.name}'s app exited ({d.folder / 'log'})")
        time.sleep(.05)
    raise TimeoutError('timeout: ' + label)


def screen_size():
    """The X screen's size, from libX11 (which the build needs anyway)."""
    try:
        x = ctypes.CDLL('libX11.so.6')
        x.XOpenDisplay.restype = ctypes.c_void_p
        x.XOpenDisplay.argtypes = [ctypes.c_char_p]
        x.XDefaultScreen.argtypes = [ctypes.c_void_p]
        x.XDisplayWidth.argtypes = x.XDisplayHeight.argtypes = [ctypes.c_void_p, ctypes.c_int]
        x.XCloseDisplay.argtypes = [ctypes.c_void_p]
        d = x.XOpenDisplay(None)
        if d:
            n = x.XDefaultScreen(d)
            size = (x.XDisplayWidth(d, n), x.XDisplayHeight(d, n))
            x.XCloseDisplay(d)
            return size
    except (OSError, AttributeError):
        pass
    return 1920, 1080


def layout(width, height):
    """Two windows side by side from the left, each at most 940 x 820. Each
    is at least 720 wide, the desktop layout's (its sidebar has Waiting to
    join): on a screen under 1500 wide, Bob's covers Alice's right edge."""
    gap = 20
    w = max(720, min(940, (width - 3 * gap) // 2))
    h = max(480, min(820, height - 180))
    y = max(0, min(60, height - h - 60))
    return [(gap, y, w, h), (max(0, min(2 * gap + w, width - w - gap)), y, w, h)]


def free_ports(n, first=47101, last=47199):
    """n ports no one listens on (the node listens on every interface)."""
    found = []
    for port in range(first, last + 1):
        with socket.socket() as s:
            try:
                s.bind(('0.0.0.0', port))
            except OSError:
                continue
        found.append(port)
        if len(found) == n:
            return found
    raise RuntimeError(f'no free TCP ports in {first}-{last}')


def running(out):
    """The pids of a demo still running from `out`."""
    pids = []
    for f in out.glob('*/pid'):
        try:
            pid = int(f.read_text())
            os.kill(pid, 0)
            if Path(f'/proc/{pid}/exe').resolve() == APP.resolve():
                pids.append(pid)
        except (ValueError, OSError):
            pass
    return pids


def start(device, geometry, args, env):
    x, y, w, h = geometry
    e = dict(env, QUIET_DB=str(device.db), QUIET_STATE=str(device.state), QUIET_TITLE=device.title,
             QUIET_X=str(x), QUIET_Y=str(y), QUIET_WIDTH=str(w), QUIET_HEIGHT=str(h))
    argv = [str(APP), *args]
    (device.folder / 'launch.json').write_text(json.dumps({
        'argv': argv, 'env': {k: v for k, v in e.items() if k.startswith('QUIET_')}}, indent=1))
    log = (device.folder / 'log').open('w')
    device.proc = sp.Popen(argv, cwd=ROOT, env=e, stdout=log, stderr=sp.STDOUT, stdin=sp.DEVNULL)
    log.close()
    (device.folder / 'pid').write_text(str(device.proc.pid))


def launch(out=OUT, bob_args=(), env=None):
    """Alice's app (seeded, its invite issued) and then Bob's, with the link."""
    env = dict(os.environ if env is None else env)
    if not APP.exists():
        raise RuntimeError("the app isn't built yet: run make install first")
    if not env.get('DISPLAY'):
        raise RuntimeError("no X display (DISPLAY is unset). Lean Quiet's Linux window needs X11 or XWayland.")
    if pids := running(out):
        raise RuntimeError(f'a demo is already running (pids {" ".join(map(str, pids))}): close its windows first')
    shutil.rmtree(out, ignore_errors=True)
    alice, bob = Device('Alice', out / 'alice'), Device('Bob', out / 'bob')
    for d in (alice, bob):
        d.folder.mkdir(parents=True)
    pa, pb = free_ports(2)
    left, right = layout(*screen_size())
    invite = alice.folder / 'invite'
    start(alice, left, ['--seed', '--name', 'Alice', '--port', str(pa), '--loopback', '--invite', str(invite)], env)
    try:
        link = wait(lambda: invite.exists() and invite.read_text().strip(), "Alice's invite", 120, [alice])
        start(bob, right, ['--port', str(pb), '--loopback', *bob_args, link], env)
    except BaseException:
        stop([alice])
        raise
    return alice, bob, (pa, pb)


def stop(devices, timeout=15):
    for d in devices:
        if d.alive():
            d.proc.terminate()
    for d in devices:
        if d.proc is not None:
            try:
                d.proc.wait(timeout)
            except sp.TimeoutExpired:
                d.proc.kill()
                d.proc.wait()


class X:
    """X input, as a person gives it (xdotool)."""

    def __init__(self, env=None):
        self.env = dict(os.environ if env is None else env)
        if not shutil.which('xdotool'):
            raise RuntimeError('this needs xdotool (on Debian or Ubuntu: sudo apt-get install xdotool)')

    def run(self, *args):
        return sp.check_output(['xdotool', *map(str, args)], env=self.env, text=True).strip()

    def window(self, device):
        if device.win is None:
            title = '^' + re.escape(device.title) + '$'
            device.win = wait(lambda: self.find(title), f"{device.name}'s window", 30, [device])
        return device.win

    def find(self, title):
        p = sp.run(['xdotool', 'search', '--name', title], env=self.env, text=True, capture_output=True)
        return p.stdout.split()[-1] if p.returncode == 0 and p.stdout.split() else None

    def click(self, device, key, timeout=30):
        x, y = wait(lambda: device.control(key), f"{device.name}: {key}", timeout, [device])
        self.focus(device)
        self.run('mousemove', '--window', self.window(device), x, y, 'click', '1')

    def focus(self, device):
        """Bring the window forward (on a narrow screen the two overlap) and
        give it the keyboard."""
        win = self.window(device)
        if self.wm():
            self.run('windowactivate', '--sync', win)
        else:
            self.run('windowraise', win)
            self.run('windowfocus', '--sync', win)

    def wm(self):
        p = sp.run(['xdotool', 'getactivewindow'], env=self.env, capture_output=True)
        return p.returncode == 0

    def type(self, device, text):
        self.focus(device)
        self.run('type', '--delay', '50', text)

    def react(self, device, emoji):
        """Point at the newest message, click Add a reaction, then emoji
        among the quick reactions."""
        ex, ey = map(int, wait(lambda: device.value('editor'), f"{device.name}'s composer", 30, [device]).split()[:2])
        self.run('mousemove', '--window', self.window(device), ex + 200, ey - 45)
        self.click(device, 'react')
        self.click(device, emoji)

    def compose(self, device, text):
        """Click the composer, type, and press Return to send."""
        ex, ey = wait(lambda: (lambda v: v and tuple(map(int, v.split()[:2])))(device.value('editor')),
                      f"{device.name}'s composer", 30, [device])
        self.focus(device)
        self.run('mousemove', '--window', self.window(device), ex + 30, ey + 4, 'click', '1')
        self.run('type', '--delay', '50', text)
        wait(lambda: len(device.lines()) > 4 and device.lines()[4] == text, f"{device.name} typed {text!r}", 30, [device])
        self.run('key', 'Return')


def join(alice, bob, x, name='Bob', timeout=90):
    """What a person does: Bob's name, Agree & Join; then Alice approves."""
    wait(lambda: bob.page() == 'App.PageId.name', "Bob's Choose a name", timeout, [alice, bob])
    x.type(bob, name)
    wait(lambda: bob.value('field') == name, f'Bob typed {name}', 30, [alice, bob])
    x.click(bob, 'Pages.Act.continue_')
    wait(lambda: bob.page() == 'App.PageId.agree', "Bob's Agree & join", 30, [alice, bob])
    x.click(bob, 'Pages.Act.agree')
    wait(lambda: bob.page() == 'App.PageId.waiting', 'Bob waits to be let in', 30, [alice, bob])
    wait(lambda: alice.asking() > 0, "Bob's request reaches Alice", timeout, [alice, bob])
    x.click(alice, 'App.PageId.requests')
    wait(lambda: alice.page() == 'App.PageId.requests', "Alice's Waiting to join", 30, [alice, bob])
    x.click(alice, 'Pages.Act.approve 0')
    wait(lambda: joined(bob), 'Bob is let in', timeout, [alice, bob])
    x.click(alice, 'App.PageId.chat')
    wait(lambda: alice.page() == 'App.PageId.chat', "Alice's #general", 30, [alice, bob])


def joined(bob):
    return bob.community() == 'Quiet' and not bob.waiting() and bob.page() == 'App.PageId.chat'


def guide(alice, bob):
    """Say what to do, and what happened, until both windows are closed."""
    say("Left: Alice's laptop, showing her community's invite. Right: Bob's laptop, which has opened")
    say("her invite link, as if she had sent it to him.")
    say("1. In Bob's window: type a name, press Enter, then click Agree & Join.")
    asked = admitted = False
    while any([alice.alive(), bob.alive()]):  # polls (reaps) both
        if not asked and alice.asking() > 0:
            asked = True
            say("2. Bob's request reached Alice's laptop. In Alice's window: click Waiting to join, then the purple ✓.")
        if not admitted and bob.community() == 'Quiet' and not bob.waiting():
            admitted = True
            say("3. Bob is in: Alice's messages are on his screen. Type in either window and it shows in the other.")
            say('   Point at a message to react to it: the reaction shows in the other window too.')
            say('Close both windows (or press Ctrl-C) to stop.')
        time.sleep(.2)


def main(argv):
    auto = '--auto' in argv
    unknown = [a for a in argv if a != '--auto']
    if unknown:
        print(f'make demo: unknown argument {unknown[0]} (ARGS=--auto does the join for you)', file=sys.stderr)
        return 2
    try:
        x = X() if auto else None
        alice, bob, (pa, pb) = launch()
    except (RuntimeError, TimeoutError) as e:
        print(f'make demo: {e}', file=sys.stderr)
        return 1
    devices = [alice, bob]
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    say('Two devices on this computer, each its own app, database and node, talking over TCP with no server')
    say(f'(Alice on port {pa}, Bob on port {pb}; their files are in {OUT})')
    try:
        if auto:
            say('Joining Bob to Alice\'s community, as you would: his name, Agree & Join, then Approve')
            join(alice, bob, x)
            x.compose(bob, "Hi Alice, it's Bob!")
            wait(lambda: alice.rows()[:1] == [('Bob', "Hi Alice, it's Bob!", False)], "Bob's hi reaches Alice", 30,
                 [alice, bob])
            x.react(alice, '❤️')
            say("Bob is in, said hi, and Alice loved it. Type in either window and it shows in the other.")
            say('Close both windows (or press Ctrl-C) to stop.')
            while any([alice.alive(), bob.alive()]):  # polls (reaps) both
                time.sleep(.2)
        else:
            guide(alice, bob)
    except KeyboardInterrupt:
        pass
    except (RuntimeError, TimeoutError) as e:
        print(f'make demo: {e}', file=sys.stderr)
        return 1
    finally:
        stop(devices)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
