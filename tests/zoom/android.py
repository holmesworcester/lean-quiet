"""Check live Android system text-size changes on the suite's own emulator."""
import os
from pathlib import Path
import socket
import subprocess as sp
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'out/zoom/android'
OUT.mkdir(parents=True, exist_ok=True)
SDK = Path(os.environ.get('ANDROID_SDK', str(Path.home()/'android-sdk')))
adb = [str(SDK/'platform-tools/adb'), '-s', 'emulator-5658']

def shell(*args):
    return sp.check_output([*adb, 'shell', *map(str,args)], text=True)

def ctl(command):
    with socket.create_connection(('127.0.0.1', 7658), timeout=30) as sock:
        sock.sendall((command+'\n').encode())
        return sock.makefile().readline().strip()

def wait(fn, timeout=90):
    until = time.monotonic()+timeout
    while time.monotonic() < until:
        try:
            value=fn()
            if value: return value
        except (OSError, ValueError): pass
        time.sleep(.2)
    raise AssertionError('timeout waiting for Android typography')

def typo():
    words=ctl('typography').split()
    return dict(zip(words[::2],map(int,words[1::2])))

def shot(name):
    (OUT/(name+'.png')).write_bytes(sp.check_output([*adb,'exec-out','screencap','-p']))

assert shell('getprop', 'ro.kernel.qemu').strip() == '1'
assert sp.check_output([*adb,'emu','avd','name'],text=True).splitlines()[0] == 'lean-quiet-zoom'
sp.run([*adb,'forward','tcp:7658','localabstract:leanquiet'],check=True)
results=[]
try:
    wait(lambda: ctl('ping') == 'pong')
    wait(lambda: typo()['dpi']==420 and typo()['cell']==39)
    ctl('theme light')
    ctl('found Text size|Alex'); ctl('wait'); ctl('channel')
    ctl('post A message with enough text to wrap across several lines as the text size grows. 日本語 café Ελληνικά שלום 12:30'); ctl('wait')
    baseline=None
    pid=shell("pidof", "com.holmes.leanquiet.zoom").strip()
    for scale in [.85,1.,1.3,2.,1.]:
        before=typo()
        stats=ctl('stats').split()
        frames=int(stats[stats.index('frames')+1])
        paints=int(stats[stats.index('paints')+1])
        shell('settings','put','system','font_scale',scale)
        def applied():
            t=typo()
            if t['dpi'] != t['osDpi']: return None
            if scale == .85: good = t['dpi'] < before['dpi']
            elif scale == 1. and baseline is not None: good = t['dpi'] == baseline['dpi']
            else: good = t['dpi'] > before['dpi']
            return t if good else None
        current=wait(applied)
        assert current['cell'] == (current['dpi']*15+80)//160, current
        assert current['cell'] <= current['line'], current
        assert current['W'] >= current['dpi']*160//160, current
        if scale==1. and baseline is None:
            baseline=current
            # The old 48px at 420 dpi was ~18.3dp; the design body is 15sp.
            assert current['cell'] < 48, current
        if results and scale > results[-1][0]:
            assert current['cell'] > results[-1][1]['cell'], (results[-1],current)
            assert current['generation'] > before['generation'], 'live resize did not retire layout caches'
        assert 'total 1' in ctl('state'), ctl('state')
        assert shell('pidof', 'com.holmes.leanquiet.zoom').strip() == pid, 'text change restarted the process'
        def painted():
            stats=ctl('stats').split()
            return int(stats[stats.index('paints')+1]) > paints
        wait(painted)
        # Allow Android's configuration freeze/crossfade to finish while
        # requiring actual subsequent app frames, then inspect real pixels.
        wait(lambda: int(ctl('stats').split()[1]) >= frames+60)
        shot('font-'+str(scale))
        from PIL import Image
        im=Image.open(OUT/('font-'+str(scale)+'.png')).convert('RGB')
        x0=round(64*current['dpi']/160)
        x1=im.width-round(12*current['dpi']/160)
        dark=[]
        for y in range(im.height//3,im.height-150):
            dark.append(sum(max(im.getpixel((x,y)))<100 for x in range(x0,x1))>=4)
        first=next(i for i,v in enumerate(dark) if v)
        last=first
        while last<len(dark) and dark[last]: last+=1
        current['inkHeight']=last-first
        assert current['cell']//2 <= current['inkHeight'] <= current['cell'], current
        if results and scale>results[-1][0]:
            assert current['inkHeight']>results[-1][1]['inkHeight'], 'OS reported larger text but displayed stale glyphs'

        results.append((scale,current))
    shell('input','keyevent','KEYCODE_HOME')
    shell('am','start','-n','com.holmes.leanquiet.zoom/com.holmes.leanquiet.LeanActivity')
    wait(lambda: typo()['cell']==baseline['cell'])
    (OUT/'result.txt').write_text('PASS live OS font changes, body size, cache generation, retained message, return to app\n'+repr(results)+'\n')
    from PIL import Image, ImageDraw
    montage=Image.new('RGB',(1080,640),'white')
    draw=ImageDraw.Draw(montage)
    for i,scale in enumerate([.85,1.,1.3,2.]):
        draw.text((i*270+10,10),f'OS text {scale*100:g}%',fill='black')
        pic=Image.open(OUT/f'font-{scale}.png').convert('RGB')
        pic.thumbnail((270,600))
        montage.paste(pic,(i*270,34))
    montage.save(OUT/'text-size-comparison.png')
    print('Android accessibility: PASS',results,flush=True)
finally:
    sp.run([*adb,'shell','settings','put','system','font_scale','1.0'],check=False)
    sp.run([*adb,'logcat','-d'],stdout=(OUT/'logcat.txt').open('w'),check=False)
    sp.run([*adb,'forward','--remove','tcp:7658'],check=False)
