#!/usr/bin/env python3
"""Drive the real AppKit window with OS input; preserve logs/frames on failure."""
import json, os, pathlib, re, signal, struct, subprocess as sp, sys, time
app, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
state, db, png = out/'state.txt', out/'test.db', out/'frame.png'
for p in [state, db, pathlib.Path(str(db)+'-wal'), pathlib.Path(str(db)+'-shm'), pathlib.Path(str(db)+'.zoom')]:
    p.unlink(missing_ok=True)
stats=out/'native-scroll.txt'
env = dict(os.environ, QUIET_DB=str(db), QUIET_STATE=str(state), QUIET_SNAPSHOT=str(png), QUIET_NATIVE_TRACE="1", QUIET_COMPOSITOR_SNAPSHOT="1", QUIET_NATIVE_SCROLL_STATS=str(stats))
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

# Use the authorized AX/CGEvent helper directly. System Events can have
# separate TCC permissions and silently expose zero windows over SSH.
input_command=[str(out/'native-input')]
sp.run(['xcrun','swiftc',str(pathlib.Path(__file__).with_name('input.swift')),'-o',input_command[0]],check=True)
sp.run([*input_command,'ready'],check=True)
# Keep the display awake only for this test process; manual locking still wins.
sp.Popen(['caffeinate','-di','-w',str(os.getpid())],stdout=sp.DEVNULL,stderr=sp.DEVNULL)
def native(*args):
    return sp.check_output([*input_command,*map(str,args)],text=True,timeout=15).strip()
def window_size():
    return list(map(int,native('window',proc.pid).split()))

def launch(seed=True, slow=False, legacy=False):
    global proc
    current=dict(env,QUIET_LEAN_FRAME_DELAY_MS='500' if slow else '16')
    if legacy: current['QUIET_DISABLE_NATIVE_SCROLL']='1'
    stats.unlink(missing_ok=True)
    proc=sp.Popen([str(app/'Contents/MacOS/LeanQuiet'),'--demo',*(['--chaos','120'] if seed else [])],env=current,stdout=log,stderr=log)
    wait(lambda: len(lines())>8 and lines()[3]=='App.PageId.chat' and int(lines()[5])>=(122 if seed else 2), 'desktop chat ready')

def stop():
    proc.terminate()
    try: proc.wait(timeout=10)
    except sp.TimeoutExpired: proc.kill();proc.wait()

def shot(name, settled=True):
    png.unlink(missing_ok=True); pathlib.Path(str(png)+'.json').unlink(missing_ok=True); pathlib.Path(str(png)+'.source.png').unlink(missing_ok=True); proc.send_signal(signal.SIGUSR1)
    wait(lambda: png.exists() and png.stat().st_size>1000,'rendered window PNG')
    data=png.read_bytes(); assert data[:8]==b'\x89PNG\r\n\x1a\n'
    size=struct.unpack('>II',data[16:24]); (out/(name+'.png')).write_bytes(data)
    wait(lambda: pathlib.Path(str(png)+'.json').exists(),'snapshot geometry sidecar')
    (out/(name+'.json')).write_bytes(pathlib.Path(str(png)+'.json').read_bytes())
    wait(lambda: pathlib.Path(str(png)+'.source.png').exists(),'snapshot source publication')
    (out/(name+'-source.png')).write_bytes(pathlib.Path(str(png)+'.source.png').read_bytes())
    if settled:
        check(size==tuple(map(int,lines()[0].split())),name+' matches shared desktop dimensions')
        meta=json.loads((out/(name+'.json')).read_text())
        check(size==tuple(meta['windowContentSize']),name+' canvas fills the actual OS window content area')
    backing=pathlib.Path(str(png)+'.backing.png')
    wait(lambda: backing.exists(),'existing compositor backing snapshot')
    (out/(name+'-backing.png')).write_bytes(backing.read_bytes())

try:
    launch()
    initial=tuple(map(int,lines()[0].split()))
    scale=initial[0]/1100
    chrome=window_size()[3]-initial[1]/scale
    check(initial==(round(1100*scale),round(760*scale)) and scale>=1,'desktop uses backing pixels')
    check(any(f'dpi {round(160*scale)} cell {round(14*scale)}' in l for l in lines()),'font raster matches native density')
    shot('desktop')
    check(int(lines()[5])>=122,'real signed chaos messages reach desktop queries')
    # AX supplies window chrome offset; desktop trace supplies the actual
    # composer's location, avoiding guesses about layout and titlebar size.
    def click_points(x,y):
        coords=window_size()
        logical_h=int(lines()[0].split()[1])/scale
        sp.run([*input_command,str(coords[0]+x),str(coords[1]+coords[3]-logical_h+y)],check=True,timeout=30)
    click_points(90,730)
    wait(lambda: 'Desktop.Context.settings' in lines(),'native settings click')
    native('key',proc.pid,53)
    wait(lambda: 'Desktop.Context.closed' in lines(),'native Escape closes settings')
    click_points(90,115)
    wait(lambda: lines()[3]=='App.PageId.chat','native channel click')
    check(True,'settings closes and channel/composer become reachable')
    coords=window_size()
    edit=next(l for l in lines() if l.startswith('editor ')).split()
    x=coords[0]+int(edit[1])/scale+6; y=coords[1]+coords[3]-760+int(edit[2])/scale+6
    print('window',coords,'editor',edit,'click',x,y,flush=True)
    sp.run([*input_command,str(x),str(y)],check=True,timeout=30)
    time.sleep(.3)
    native('text',proc.pid,'Mac shared desktop test')
    wait(lambda: lines()[4]=='Mac shared desktop test','native OS typing reaches Lean composer')
    before=int(lines()[5]); native('key',proc.pid,36)
    wait(lambda: int(lines()[5])==before+1 and lines()[4]=='','native Return stores message')
    check(True,'native click, typing and Return send through actual desktop app')
    native('key',proc.pid,24,'command')
    wait(lambda: any(l.startswith('zoom 110 ') for l in lines()),'Command+plus zoom')
    native('key',proc.pid,29,'command')
    wait(lambda: any(l.startswith('zoom 100 ') for l in lines()),'Command+0 reset')
    check(True,'native zoom uses shared desktop levels')
    native('window',proc.pid,640,788)
    wait(lambda: lines()[0].split()[0]==str(round(640*scale)),'native narrow resize')
    shot('narrow')
    check(int(lines()[5])==before+1,'resize retains messages')
    native('window',proc.pid,800,720)
    wait(lambda: lines()[0].split()[0]==str(round(800*scale)),'wide layout before edge drags')
    pos=window_size()
    logical_h=int(lines()[0].split()[1])/scale
    sp.run([*input_command,'scroll',str(pos[0]+600),str(pos[1]+pos[3]-logical_h+300),'160',str(proc.pid)],check=True,timeout=20)
    wait(lambda: int(lines()[7])>2000,'older messages before resizing')
    # Real edge drags exercise AppKit's tracking run loop and backing-store
    # resize behavior, which an AX set-size call does not cover.
    for label,dx,dy in [('shrink',-60,-208),('grow',280,240)]:
        pos=window_size()
        mover=sp.Popen([*input_command,
            'resize',str(pos[0]+pos[2]-1),str(pos[1]+pos[3]-1),str(dx),str(dy)])
        try:
            wait(lambda: 'liveResize 1' in stats.read_text(),'OS edge drag starts',timeout=15)
            shot('resize-'+label+'-live',settled=False)
            meta=json.loads((out/('resize-'+label+'-live.json')).read_text())
            check(meta['liveResize'],'snapshot taken while the mouse holds the window edge')
            check(not meta['native'],'stale native viewport hidden during live resize')
            assert mover.wait(timeout=15)==0
            actual=window_size()
            wait(lambda: tuple(map(int,lines()[0].split()))==(round(actual[2]*scale),round((actual[3]-chrome)*scale)),'both resized dimensions match the OS window')
            wait(lambda: re.search(r'native 1 .*liveResize 0',stats.read_text()),'native scrolling restored after resize')
            shot('resize-'+label+'-settled')
            settled=json.loads((out/('resize-'+label+'-settled.json')).read_text())
            check(settled['planeWidth']==settled['textureWidth'],'native scroll texture matches resized plane')
            check(int(lines()[5])==before+1,'edge resize retains stored messages')
        finally:
            if mover.poll() is None: mover.kill();mover.wait()

    pos=window_size()
    logical_h=int(lines()[0].split()[1])/scale
    sp.run([*input_command,'scroll',str(pos[0]+600),str(pos[1]+pos[3]-logical_h+300),'-400',str(proc.pid)],check=True,timeout=20)
    wait(lambda: int(lines()[7])==0,'native scroll returns to newest messages after resize')
    check(True,'native scrolling remains usable after grow/shrink')
    stop();state.unlink(missing_ok=True);launch(seed=False)
    wait(lambda: int(lines()[5])==before+1,'stored message survives process restart')
    check(True,'desktop database survives restart')
    shot('reopened')
    stop();state.unlink(missing_ok=True)
    def scroll_stats():
        try:
            m=re.match(r'presentations (\d+) scrollUpdates (\d+) offset (-?\d+) native (\d+) box (\d+) (\d+) (\d+) (\d+)',stats.read_text())
            return tuple(map(int,m.groups())) if m else None
        except FileNotFoundError: return None
    def scroll_input(x,y,count=40,click=False):
        pos=window_size()
        logical_h=int(lines()[0].split()[1])/scale
        return sp.Popen([*input_command,
            'scroll-click' if click else 'scroll',str(pos[0]+x),str(pos[1]+pos[3]-logical_h+y),str(count),str(proc.pid)])
    results={}
    for legacy in [False,True]:
        launch(seed=False,slow=True,legacy=legacy)
        wait(lambda: scroll_stats() is not None,'native scroll diagnostics')
        shot('legacy-before' if legacy else 'native-before')
        before=scroll_stats()
        mover=scroll_input(600,350,click=not legacy)
        samples=[]
        captured=False
        try:
            end=time.monotonic()+20
            while mover.poll() is None and time.monotonic()<end:
                s=scroll_stats()
                if s:
                    samples.append(s)
                    if not legacy and not captured and s[1]-before[1]>=3:
                        shot('native-in-flight'); captured=True
                time.sleep(.01)
            assert mover.wait(timeout=5)==0
        finally:
            if mover.poll() is None: mover.kill();mover.wait()
        time.sleep(.2)
        after=scroll_stats()
        changes={}
        for sample in samples:
            changes.setdefault(sample[0],set()).add(sample[1])
        independent=max((max(v)-min(v) for v in changes.values()),default=0)
        results['legacy' if legacy else 'native']={'before':before,'after':after,'updates_without_Lean_frame':independent,'samples':samples}
        if legacy:
            check(after[1]==0 and independent==0,'negative control detects wheel scrolling coupled to Lean frames')
        else:
            check(captured,'captured native scrolling between Lean publications')
            check(after[3]==1 and after[1]-before[1]>=10 and independent>=3,
                'native scroll advances repeatedly while Lean frames are delayed by 500ms')
            check(after[2]>before[2]+100,'native OS wheel reaches older content')
            box=after[4:]
            check(box[0]==round(220*scale) and box[1]>0 and box[1]+box[3]<round(760*scale),
                'native viewport excludes sidebar, header and composer/toolbar')
            wait(lambda: int(lines()[7])>100,'Lean catches native position')
            wait(lambda: any(s.startswith('tap 2 ') for s in lines()),'moving-message touch uses shared mobile frame/slide classifier')
            check(int(re.search(r'rawTouches (\d+)',stats.read_text())[1])>=2,'native moving click sends mobile raw down/up with the displayed frame')
            shot('native-scrolled')
        stop();state.unlink(missing_ok=True)
    (out/'scroll-comparison.json').write_text(json.dumps(results,indent=2)+'\n')
    print(f'{checks} Mac desktop checks passed',flush=True)
finally:
    if proc and proc.poll() is None: stop()
    log.close()
