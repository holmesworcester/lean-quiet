#!/usr/bin/env python3
"""leanquiet:// links on the Linux desktop, through install.sh's launcher and
menu entry in private HOME/XDG folders, on a private X display:

  a cold start takes the link in its arguments;
  a warm start (xdg-open through the menu entry, or a second launch) hands
  the link to the running instance, which asks to be raised, and exits;
  an instance of another database is never used; a stale socket is replaced.

Which link the app took is read from QUIET_STATE: `invite <text>` once it
opens the join page, `toast <due> <text>` when it refuses the link. A link in
the scheme Community.Invite.text writes (read from a real invite) must open
the join page with exactly that invite; until ops/community/Link.lean writes
leanquiet://, a leanquiet:// link must at least reach the app (its refusal
toast). Every process started here is reaped; nothing outside out/ and a
private runtime folder is written."""
import os
from pathlib import Path
import select
import shutil
import signal
import socket
import stat
import subprocess as sp
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/linux-links'
BIN = ROOT / '.lake/build/bin'
checks = 0
procs = []


def check(ok, label):
    global checks
    assert ok, label
    checks += 1
    print('ok', label, flush=True)


def wait(fn, label, timeout=60):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        value = fn()
        if value:
            return value
        time.sleep(.05)
    raise AssertionError('timeout: ' + label)


def lines(state):
    try:
        return state.read_text().splitlines()
    except FileNotFoundError:
        return []


def field(state, key):
    return next((s[len(key) + 1:] for s in lines(state) if s.startswith(key + ' ')), None)


shutil.rmtree(OUT, ignore_errors=True)
OUT.mkdir(parents=True)
# The real install, which nothing here may touch.
real = [Path.home() / p for p in ['.local/opt/lean-quiet', '.local/bin/lean-quiet',
                                  '.local/share/applications', '.config/mimeapps.list']]
before_real = {p: p.stat().st_mtime_ns for p in real if p.exists()}

# A real invite, from the app's own Community.Invite.text.
links = []
for i in range(6):
    sp.run([str(BIN / 'invite_link'), str(OUT / f'invite{i}')], check=True, stdout=sp.DEVNULL)
    links.append((OUT / f'invite{i}/invite').read_text().strip())
# The app shares the join page link; the page opens leanquiet://join/ and the
# same fields, which is what the desktop hands the app.
web = 'https://holmesworcester.github.io/lean-quiet/join#'
assert all(t.startswith(web) for t in links), links[0]
native = 'leanquiet://join/'
payload = [t[len(web):] for t in links]
print('Community.Invite.text writes', web, '; the page opens', native, flush=True)


def link(scheme, n):
    return f'{scheme}://join/{payload[n]}'


def took(state, url, after):
    """The app's state shows it took url, later than the toast deadline `after`."""
    if url.startswith(native):
        return field(state, 'invite') == web + url[len(native):] and 'App.PageId.name' in lines(state)
    toast = field(state, 'toast')
    if toast:
        due, text = toast.split(' ', 1)
        return int(due) > after and text == "That isn't a Quiet invite link."
    return False


def toast_due(state):
    toast = field(state, 'toast')
    return int(toast.split(' ', 1)[0]) if toast else 0


home = OUT / 'home'
data = home / '.local/share'
config = home / '.config'
for d in [data, config, OUT / 'system/share', OUT / 'system/etc']:
    d.mkdir(parents=True)
# sun_path holds 108 bytes, so the runtime folder is short.
run = Path(tempfile.mkdtemp(prefix='lql-', dir=os.environ.get('TMPDIR', '/mnt/storage/holmes-tmp')))
browser = OUT / 'browser'
browser.write_text(f'#!/bin/sh\necho "$@" >> {OUT / "browser-called"}\n')
browser.chmod(0o755)
env = {k: v for k, v in os.environ.items()
       if k not in {'XDG_CURRENT_DESKTOP', 'XDG_SESSION_DESKTOP', 'DESKTOP_SESSION', 'KDE_FULL_SESSION',
                    'GNOME_DESKTOP_SESSION_ID', 'MATE_DESKTOP_SESSION_ID', 'QUIET_DB', 'QUIET_STATE', 'DISPLAY'}}
# xdg-open's generic path: no desktop session, no session bus to find one;
# a browser that only records a call, which must not happen.
env.update(HOME=str(home), XDG_DATA_HOME=str(data), XDG_CONFIG_HOME=str(config),
           XDG_CACHE_HOME=str(home / '.cache'), XDG_RUNTIME_DIR=str(run),
           XDG_DATA_DIRS=str(OUT / 'system/share'), XDG_CONFIG_DIRS=str(OUT / 'system/etc'),
           DBUS_SESSION_BUS_ADDRESS='disabled:', BROWSER=str(browser))

try:
    # (d) install.sh from the repository build, and from a release folder.
    p = sp.run(['sh', str(ROOT / 'platforms/linux/install.sh')], env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True)
    (OUT / 'install.log').write_text(p.stdout)
    check(p.returncode == 0, 'install.sh installs a repository build: ' + p.stdout.strip().splitlines()[-1])
    prefix = home / '.local'
    launcher = prefix / 'bin/lean-quiet'
    exe = prefix / 'opt/lean-quiet/lean-quiet'
    entry = (prefix / 'share/applications/lean-quiet.desktop').read_text().splitlines()
    check(f'Exec={launcher} %u' in entry and not any(s.startswith('Exec=') and '"' in s for s in entry),
          'the menu entry runs the launcher, unquoted, with %u')
    check('MimeType=x-scheme-handler/leanquiet;' in entry, 'the menu entry handles x-scheme-handler/leanquiet')
    check(exe.read_bytes() == (BIN / 'linux').read_bytes() and (prefix / 'opt/lean-quiet/assets/font.bin').exists()
          and (prefix / 'share/icons/hicolor/scalable/apps/lean-quiet.svg').exists(),
          'the program, its assets and the icon are installed')
    query = sp.run(['xdg-mime', 'query', 'default', 'x-scheme-handler/leanquiet'], env=env, stdout=sp.PIPE, text=True)
    check(query.stdout.strip() == 'lean-quiet.desktop' and
          'x-scheme-handler/leanquiet=lean-quiet.desktop' in (config / 'mimeapps.list').read_text(),
          'xdg-mime names the entry the default leanquiet:// handler, in the private config')
    release = OUT / 'release'
    release.mkdir()
    os.link(BIN / 'linux', release / 'lean-quiet')
    sp.run(['cp', '-al', str(ROOT / 'assets'), str(release / 'assets')], check=True)
    for f in ['install.sh', 'lean-quiet.svg']:
        shutil.copy(ROOT / 'platforms/linux' / f, release / f)
    p = sp.run(['sh', str(release / 'install.sh')], env=dict(env, PREFIX=str(OUT / 'prefix')),
               stdout=sp.PIPE, stderr=sp.STDOUT, text=True)
    (OUT / 'install-release.log').write_text(p.stdout)
    check(p.returncode == 0 and (OUT / 'prefix/opt/lean-quiet/lean-quiet').read_bytes() == exe.read_bytes() and
          f'Exec={OUT}/prefix/bin/lean-quiet %u' in (OUT / 'prefix/share/applications/lean-quiet.desktop').read_text(),
          'install.sh installs a release folder (lean-quiet, assets/, install.sh, icon) into a PREFIX')
    # The desktops' own openers find the entry too: exo-open on XFCE, gio on
    # GNOME. A launcher that records its arguments stands in for the app.
    opened = OUT / 'opened'
    (OUT / 'prefix/bin/lean-quiet').write_text(f'#!/bin/sh\necho "$@" > {opened}\n')
    for de, opener in [('XFCE', 'exo-open'), ('GNOME', 'gio')]:
        if not shutil.which(opener):
            print(f'SKIP {de}: no {opener}', flush=True)
            continue
        opened.unlink(missing_ok=True)
        p = sp.run(['xdg-open', link('leanquiet', 0)], env=dict(env, XDG_DATA_HOME=str(OUT / 'prefix/share'),
                   XDG_CURRENT_DESKTOP=de), stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=30)
        check(p.returncode == 0 and opened.exists() and opened.read_text().strip() == link('leanquiet', 0),
              f'xdg-open on {de} ({opener}) runs the entry with the link')
    p = sp.run(['sh', str(release / 'install.sh')], env=dict(env, PREFIX=str(OUT / 'with space')),
               stdout=sp.PIPE, stderr=sp.STDOUT, text=True)
    check(p.returncode != 0 and 'an unquoted Exec cannot hold' in p.stdout and not (OUT / 'with space').exists(),
          'a PREFIX with a space fails loudly instead of writing a quoted Exec')

    # A private X display, as platforms/linux/test.py starts it.
    read_fd, write_fd = os.pipe()
    with (OUT / 'xvfb.log').open('w') as log:
        xvfb = sp.Popen(['Xvfb', '-displayfd', str(write_fd), '-screen', '0', '1600x1200x24', '-nolisten', 'tcp', '-ac'],
                        pass_fds=(write_fd,), stdout=log, stderr=log)
    procs.append(xvfb)
    os.close(write_fd)
    assert select.select([read_fd], [], [], 10)[0], 'Xvfb did not start'
    number = os.read(read_fd, 32).decode().strip()
    os.close(read_fd)
    assert number.isdigit(), 'Xvfb cannot create a local display; see out/linux-links/xvfb.log'
    env['DISPLAY'] = ':' + number

    def windows():
        p = sp.run(['xdotool', 'search', '--name', '^Lean Quiet$'], env=env, stdout=sp.PIPE, text=True)
        return set(p.stdout.split())

    def instances():
        found = set()
        for d in Path('/proc').iterdir():
            try:
                if d.name.isdigit() and os.readlink(d / 'exe') == str(exe):
                    found.add(int(d.name))
            except OSError:
                pass
        return found

    def start(name, *args, db=None):
        """The launcher, as a menu or a link would run it; QUIET_STATE per run."""
        e = dict(env, QUIET_STATE=str(OUT / (name + '.state')))
        if db:
            e['QUIET_DB'] = str(OUT / db)
        shown = windows()
        proc = sp.Popen([str(launcher), '--offline', *args], env=e, stdout=sp.DEVNULL, stderr=sp.DEVNULL)
        procs.append(proc)
        return proc, OUT / (name + '.state'), shown

    def window_of(shown, label):
        return wait(lambda: next(iter(windows() - shown), None), label)

    def close(proc, win, label):
        sp.run(['xdotool', 'windowclose', win], env=env, check=True)
        proc.wait(timeout=30)
        check(proc.returncode == 0, label)

    def sockets():
        return sorted(p.name for p in (run / 'lean-quiet').glob('*.sock'))

    watch = sp.Popen([str(OUT.parent / 'linux/active_watch')], env=env, stdout=sp.PIPE, text=True)
    procs.append(watch)
    assert watch.stdout.readline().strip() == 'ready'
    heard = []

    def activations():
        while select.select([watch.stdout], [], [], 0)[0]:
            heard.append(watch.stdout.readline().strip())
        return heard

    # (a) Cold: the link in the launcher's arguments.
    a, a_state, shown = start('a', link('leanquiet', 0))
    a_win = window_of(shown, 'the instance maps its window')
    wait(lambda: took(a_state, link('leanquiet', 0), 0), 'cold start: the app takes the link in its arguments')
    check(True, 'cold start: the app takes the leanquiet:// link in its arguments' +
          (' (join page)' if native.startswith('leanquiet') else ' (refusal toast until Link.lean writes leanquiet://)'))
    wm_class = sp.check_output(['xprop', '-id', a_win, 'WM_CLASS'], env=env, text=True).strip()
    check(wm_class == 'WM_CLASS(STRING) = "lean-quiet", "lean-quiet"' and 'StartupWMClass=lean-quiet' in entry,
          'the window\'s WM_CLASS matches the menu entry\'s StartupWMClass')
    folder = run / 'lean-quiet'
    sock = folder / sockets()[0]
    check(stat.S_IMODE(folder.stat().st_mode) == 0o700 and stat.S_ISSOCK(sock.stat().st_mode) and
          stat.S_IMODE(sock.stat().st_mode) == 0o600 and len(sockets()) == 1,
          'one socket, 0600, in a 0700 folder of XDG_RUNTIME_DIR')
    check(instances() == {a.pid}, 'one instance runs the installed program')

    # (b) Warm: xdg-open, through the menu entry, in the private XDG folders.
    for n, how in [(1, 'xdg-open'), (2, 'launcher')]:
        url = link('leanquiet', n)
        after = toast_due(a_state)
        activations(); heard.clear()
        if how == 'xdg-open':
            p = sp.run(['xdg-open', url], env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=60)
        else:
            p = sp.run([str(launcher), url], env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True, timeout=60)
        (OUT / f'warm-{n}.log').write_text(p.stdout)
        check(p.returncode == 0, f'warm {how}: the second launch hands the link over and exits 0')
        wait(lambda: took(a_state, url, after), f'warm {how}: the running instance takes the link')
        check(True, f'warm {how}: the running instance takes the leanquiet:// link')
        check(instances() == {a.pid} and a.poll() is None, f'warm {how}: no second process stays alive')
        wait(lambda: f'active {int(a_win):#x} 2' in activations(), f'warm {how}: _NET_ACTIVE_WINDOW')
        check(True, f'warm {how}: the instance asks the window manager to raise its window')
    check(not (OUT / 'browser-called').exists(), 'xdg-open never fell back to the browser')
    # The old scheme passes through the same socket untouched: the join page
    # with exactly this invite while Link.lean still writes quiet://.
    url = link('quiet', 3)
    after = toast_due(a_state)
    p = sp.run([str(launcher), url], env=env, timeout=60)
    check(p.returncode == 0, 'warm: a quiet:// link is handed over too')
    wait(lambda: took(a_state, url, after), 'warm: the instance takes the quiet:// link')
    check(True, 'warm: the link text reaches Lean unchanged (' +
          ('join page with this invite' if url.startswith(native) else 'refusal toast once Link.lean writes leanquiet://') + ')')
    activations(); heard.clear()
    p = sp.run([str(launcher)], env=env, timeout=60)
    check(p.returncode == 0, 'a plain second launch exits 0')
    wait(lambda: f'active {int(a_win):#x} 2' in activations(), 'plain second launch raises the window')
    check(instances() == {a.pid}, 'a plain second launch raises the running window instead of opening another')

    # (c) Another database's instance is never used.
    a_before = (field(a_state, 'invite'), toast_due(a_state))
    b, b_state, shown = start('b', db='b.db')
    b_win = window_of(shown, 'a second database gets its own instance')
    wait(lambda: len(sockets()) == 2, 'its own socket')
    c, c_state, shown = start('c', link('leanquiet', 4), db='c.db')
    c_win = window_of(shown, 'a third database gets its own instance')
    wait(lambda: took(c_state, link('leanquiet', 4), 0), 'the third database\'s instance takes its own link')
    check(c.poll() is None and len(sockets()) == 3 and field(b_state, 'invite') is None and
          field(b_state, 'toast') is None and (field(a_state, 'invite'), toast_due(a_state)) == a_before,
          'a launch on another database never uses a running instance\'s socket')
    close(c, c_win, 'the third instance closes cleanly')
    check(len(sockets()) == 2, 'a closed instance removes its socket')

    # A stale socket: an instance killed outright leaves its socket file.
    b_socks = set(sockets())
    os.kill(b.pid, signal.SIGKILL)
    b.wait(timeout=10)
    check(set(sockets()) == b_socks, 'a killed instance leaves a stale socket')
    b2, b2_state, shown = start('b2', link('leanquiet', 5), db='b.db')
    b2_win = window_of(shown, 'a launch after a stale socket becomes the instance')
    wait(lambda: took(b2_state, link('leanquiet', 5), 0), 'the new instance takes its link')
    check(b2.poll() is None and set(sockets()) == b_socks, 'a stale socket is replaced by the new instance\'s')
    after = toast_due(b2_state)
    c2 = sp.run([str(launcher), link('leanquiet', 2)], env=dict(env, QUIET_DB=str(OUT / 'b.db')), timeout=60)
    check(c2.returncode == 0, 'a later launch on that database hands its link over')
    wait(lambda: took(b2_state, link('leanquiet', 2), after), 'the new instance answers on the replaced socket')
    check(True, 'the new instance answers on the replaced socket')
    check(instances() == {a.pid, b2.pid}, 'one instance per database')
    close(b2, b2_win, 'the replacing instance closes cleanly')
    close(a, a_win, 'the first instance closes cleanly')
    check(sockets() == [], 'every socket is removed on a clean exit')
    after_real = {p: p.stat().st_mtime_ns for p in real if p.exists()}
    check(after_real == before_real, 'the real install and mime defaults are untouched')
    print(f'linux links: {checks} checks', flush=True)
finally:
    for proc in reversed(procs):
        if proc.poll() is None:
            proc.terminate()
            try:
                proc.wait(timeout=10)
            except sp.TimeoutExpired:
                proc.kill()
                proc.wait()
    shutil.rmtree(run, ignore_errors=True)
