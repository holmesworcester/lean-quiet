#!/usr/bin/env python3
"""Drive the real AppKit window with OS input; preserve logs/frames on failure."""
import os, pathlib, re, signal, struct, subprocess as sp, sys, time
app, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
state, db, png = out/'state.txt', out/'test.db', out/'frame.png'
for p in [state, db, pathlib.Path(str(db)+'-wal'), pathlib.Path(str(db)+'-shm'), pathlib.Path(str(db)+'.zoom')]:
    p.unlink(missing_ok=True)
env = dict(os.environ, QUIET_DB=str(db), QUIET_STATE=str(state), QUIET_SNAPSHOT=str(png), QUIET_NATIVE_TRACE="1")
log = (out/'app.log').open('w')
proc = None
checks = 0

def wait(fn, label, timeout=40):
    end=time.monotonic()+timeout
    while time.monotonic()<end:
        if proc.poll() is not None: raise AssertionError(f'app exited {proc.returncode}: {label}')
        value=fn()
        if value: return value
        time.sleep(.1)
    raise AssertionError('timeout: '+label)

def lines():
    try: return state.read_text().splitlines()
    except FileNotFoundError: return []

def check(ok, label):
    global checks
    assert ok, label
    checks+=1; print('ok',label,flush=True)

def osa(body):
    script=f'tell application "System Events"\n tell first process whose unix id is {proc.pid}\n set frontmost to true\n {body}\n end tell\nend tell'
    return sp.check_output(['osascript','-e',script], text=True, timeout=15).strip()

def launch(seed=True):
    global proc
    proc=sp.Popen([str(app/'Contents/MacOS/LeanQuiet'),'--demo',*(['--chaos','120'] if seed else [])],env=env,stdout=log,stderr=log)
    wait(lambda: len(lines())>8 and lines()[3]=='App.PageId.chat' and int(lines()[5])>=(122 if seed else 2), 'desktop chat ready')

def stop():
    proc.terminate()
    try: proc.wait(timeout=10)
    except sp.TimeoutExpired: proc.kill();proc.wait()

def shot(name):
    png.unlink(missing_ok=True); proc.send_signal(signal.SIGUSR1)
    wait(lambda: png.exists() and png.stat().st_size>1000,'rendered window PNG')
    data=png.read_bytes(); assert data[:8]==b'\x89PNG\r\n\x1a\n'
    size=struct.unpack('>II',data[16:24]); (out/(name+'.png')).write_bytes(data)
    check(size==tuple(map(int,lines()[0].split())),name+' matches shared desktop dimensions')

try:
    launch()
    initial=tuple(map(int,lines()[0].split()))
    scale=initial[0]/1100
    check(initial==(round(1100*scale),round(760*scale)) and scale>=1,'desktop uses backing pixels')
    check(any(f'dpi {round(160*scale)} cell {round(14*scale)}' in l for l in lines()),'font raster matches native density')
    shot('desktop')
    check(int(lines()[5])>=122,'real signed chaos messages reach desktop queries')
    # AX supplies window chrome offset; desktop trace supplies the actual
    # composer's location, avoiding guesses about layout and titlebar size.
    def click_points(x,y):
        coords=list(map(int,re.findall(r'-?\d+',osa('get {position of window 1, size of window 1}'))))
        logical_h=int(lines()[0].split()[1])/scale
        sp.run(['xcrun','swift',str(pathlib.Path(__file__).with_name('input.swift')),str(coords[0]+x),str(coords[1]+coords[3]-logical_h+y)],check=True,timeout=30)
    click_points(90,730)
    wait(lambda: 'Desktop.Context.settings' in lines(),'native settings click')
    osa('key code 53')
    wait(lambda: 'Desktop.Context.closed' in lines(),'native Escape closes settings')
    click_points(90,115)
    wait(lambda: lines()[3]=='App.PageId.chat','native channel click')
    check(True,'settings closes and channel/composer become reachable')
    coords=list(map(int,re.findall(r'-?\d+',osa('get {position of window 1, size of window 1}'))))
    edit=next(l for l in lines() if l.startswith('editor ')).split()
    x=coords[0]+int(edit[1])/scale+6; y=coords[1]+coords[3]-760+int(edit[2])/scale+6
    print('window',coords,'editor',edit,'click',x,y,flush=True)
    sp.run(['xcrun','swift',str(pathlib.Path(__file__).with_name('input.swift')),str(x),str(y)],check=True,timeout=30)
    time.sleep(.3)
    osa('keystroke "Mac shared desktop test"')
    wait(lambda: lines()[4]=='Mac shared desktop test','native OS typing reaches Lean composer')
    before=int(lines()[5]); osa('key code 36')
    wait(lambda: int(lines()[5])==before+1 and lines()[4]=='','native Return stores message')
    check(True,'native click, typing and Return send through actual desktop app')
    osa('keystroke "=" using command down')
    wait(lambda: any(l.startswith('zoom 110 ') for l in lines()),'Command+plus zoom')
    osa('keystroke "0" using command down')
    wait(lambda: any(l.startswith('zoom 100 ') for l in lines()),'Command+0 reset')
    check(True,'native zoom uses shared desktop levels')
    osa('set size of window 1 to {640, 788}')
    wait(lambda: lines()[0].split()[0]==str(round(640*scale)),'native narrow resize')
    shot('narrow')
    check(int(lines()[5])==before+1,'resize retains messages')
    stop();state.unlink(missing_ok=True);launch(seed=False)
    wait(lambda: int(lines()[5])==before+1,'stored message survives process restart')
    check(True,'desktop database survives restart')
    shot('reopened')
    print(f'{checks} Mac desktop checks passed',flush=True)
finally:
    if proc and proc.poll() is None: stop()
    log.close()
