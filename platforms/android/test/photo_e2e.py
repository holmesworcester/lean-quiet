"""Real Android system picker, through its native UI and the app's composer."""
import argparse
import os
from pathlib import Path
import re
import socket
import subprocess as sp
import time
import xml.etree.ElementTree as ET

p = argparse.ArgumentParser()
p.add_argument('serial'); p.add_argument('out', type=Path); p.add_argument('--port', type=int, default=7592)
a = p.parse_args(); a.out.mkdir(parents=True, exist_ok=True)
adb = [str(Path(os.environ.get('ANDROID_SDK', str(Path.home()/'android-sdk')))/'platform-tools/adb'), '-s', a.serial]

def shell(*args):
    return sp.check_output([*adb, 'shell', *args], text=True)

def ctl(command):
    with socket.create_connection(('127.0.0.1', a.port), timeout=60) as s:
        s.sendall((command+'\n').encode())
        return s.makefile().readline().strip()

def wait(fn, timeout=60):
    end = time.monotonic()+timeout
    while time.monotonic() < end:
        try:
            result = fn()
            if result: return result
        except (ConnectionError, OSError): pass
        time.sleep(.3)
    raise AssertionError('timed out waiting for native photo state')

def ui():
    shell('uiautomator', 'dump', '/sdcard/quiet-photo-ui.xml')
    text = shell('cat', '/sdcard/quiet-photo-ui.xml')
    (a.out/'picker.xml').write_text(text)
    return ET.fromstring(text).iter('node')

def click(node):
    x0,y0,x1,y1 = map(int, re.findall(r'\d+', node.attrib['bounds']))
    shell('input', 'tap', str((x0+x1)//2), str((y0+y1)//2))

def shot(name):
    (a.out/f'{name}.png').write_bytes(sp.check_output([*adb,'exec-out','screencap','-p']))

sp.run([*adb,'forward',f'tcp:{a.port}','localabstract:leanquiet'],check=True)
try:
    wait(lambda: ctl('ping') == 'pong')
    ctl('found Photo picker|Ann'); ctl('wait'); ctl('channel')
    assert ctl('photo-status').startswith('photos 0 pending false')
    ctl('pick-photo')
    wait(lambda: any('photopicker' in n.attrib.get('package','') or n.attrib.get('resource-id','').endswith('/privacy_text') or n.attrib.get('content-desc') == 'Photos' for n in ui()))
    shot('picker-cancel')
    shell('input', 'keyevent', 'KEYCODE_BACK')
    wait(lambda: ctl('photo-status').startswith('photos 0 pending false'))
    ctl('pick-photo')
    def select():
        nodes = list(ui())
        # The suite's private emulator gallery contains only its seeded image.
        candidates = [n for n in nodes if n.attrib.get('resource-id','').endswith('/icon_thumbnail')]
        if not candidates:
            candidates = [n for n in nodes if n.attrib.get('resource-id','').endswith('/image') and n.attrib.get('content-desc')]
        if not candidates:
            candidates = [n for n in nodes if n.attrib.get('content-desc','').startswith('Photo taken on')]
        if candidates: click(candidates[0]); return True
    wait(select)
    # Some system picker versions show a confirmation button after selection.
    time.sleep(.5)
    for n in ui():
        if n.attrib.get('text') in ['Add', 'Open', 'Done'] and n.attrib.get('enabled') == 'true':
            click(n); break
    result = wait(lambda: (r if r.startswith('photos 1 pending false') else None) if (r := ctl('photo-status')) else None, 120)
    assert '(1024, 2048)' in result, result
    shot('selected-oriented-photo')
    ctl('post Native picker photo'); ctl('wait')
    wait(lambda: any('Native picker photo' in row and ' painted' in row for row in ctl('pics').split(' | ')))
    assert ctl('photo-status').startswith('photos 0 pending false')
    shot('sent-photo')
    (a.out/'result.txt').write_text('PASS cancellation, actual system selection, EXIF orientation, bounded decode, composer attachment and send\n'+result+'\n')
    print((a.out/'result.txt').read_text())
finally:
    sp.run([*adb,'logcat','-d'], stdout=(a.out/'logcat.txt').open('w'))
    try: shot('final')
    except sp.CalledProcessError: pass
    sp.run([*adb,'forward','--remove',f'tcp:{a.port}'],check=False)
