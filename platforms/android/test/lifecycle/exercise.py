#!/usr/bin/env python3
"""Real NativeActivity recreation, native runtime retention, IME and final exit.

A separate instrumentation APK drives Activity.recreate/finish. Assertions use
actual OS PID/window/IME observations and the running twin's control socket.
"""
from pathlib import Path
import argparse, json, os, re, socket, subprocess, time
from crashes import crash_lines

ROOT = Path(__file__).resolve().parents[4]
PKG = 'com.holmes.leanquiet'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--serial', required=True)
    parser.add_argument('--apk', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--ime-prepared', action='store_true', help='suite already installed this unchanged IME once')
    args = parser.parse_args()
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=True)
    adb = [str(Path(os.environ.get('ANDROID_SDK', Path.home()/'android-sdk'))/'platform-tools/adb'), '-s', args.serial]
    passed, failures = [], []
    instrumentation = None; port = None
    run_token = os.urandom(16).hex()

    def run(*arguments, check=True, timeout=15):
        return subprocess.run(adb+list(arguments), capture_output=True, text=True, timeout=timeout, check=check).stdout.strip()

    def pid(): return run('shell', 'pidof', PKG, check=False)

    def until(seconds, predicate):
        deadline = time.monotonic()+seconds
        while time.monotonic()<deadline:
            try:
                value = predicate()
                if value: return value
            except (OSError, ValueError, subprocess.SubprocessError): pass
            time.sleep(.02)
        return False

    def ok(label, value):
        if value:
            passed.append(label); print('ok: '+label, flush=True)
        else:
            failures.append(label); print('FAIL: '+label, flush=True)
            raise AssertionError(label)

    def state():
        with socket.create_connection(('127.0.0.1',port), timeout=.3) as stream:
            stream.sendall(b'state\n')
            return stream.makefile(encoding='utf-8').readline().strip()

    def ctl(command):
        with socket.create_connection(('127.0.0.1',port), timeout=.3) as stream:
            stream.sendall((command+'\n').encode())
            return stream.makefile(encoding='utf-8').readline().strip()

    def field(name):
        found=re.search(r'(?:^| )'+name+r'=([^ ]+)',state())
        return int(found.group(1)) if found else -1

    def native_text(): return state().split('text=',1)[1].split(' pos=',1)[0]

    def phase():
        # A prior crashed/finished instrumentation run can leave a ready file.
        # Only observations from this actual invocation satisfy its handshake.
        observed = run('shell','run-as',PKG,'cat','files/lifecycle-state',check=False).split()
        return observed[:3] if len(observed)==4 and observed[3]==run_token else []

    def command(value):
        # value is a fixed fixture command, never external shell content.
        run('shell','run-as',PKG,'sh','-c',f"'printf %s {value} > files/lifecycle-command'")

    try:
        run('shell','am','force-stop',PKG)
        run('install','-r',str(args.apk.resolve()),timeout=40)
        run('install','-r',str(ROOT/'out/lifecycle-probe.apk'),timeout=40)
        if not args.ime_prepared:
            # Unbind the old service before replacing its APK. Replacing the
            # selected IME can leave a dangling system_server binding record.
            (out/'ime-reset.txt').write_text(run('shell','ime','reset'))
            run('install','-r',str(ROOT/'out/testime.apk'),timeout=40)
        # PackageManager installation returns before package-replacement
        # broadcasts update the running IME registry/binding. Flush those
        # actual OS queues before measuring any application latency.
        (out/'package-broadcast-barrier.txt').write_text(run('shell','am','wait-for-broadcast-idle','--flush-broadcast-loopers',timeout=30))
        ok('OS registers the installed test IME',until(5,lambda: 'com.holmes.testime/.TestIme' in run('shell','ime','list','-a','-s')))
        run('shell','ime','enable','com.holmes.testime/.TestIme')
        run('shell','ime','set','com.holmes.testime/.TestIme')
        run('logcat','-c')
        port=int(run('forward','tcp:0','localabstract:leanquiet'))
        log=(out/'instrumentation.log').open('w')
        instrumentation=subprocess.Popen(adb+['shell','am','instrument','-w','-e','runToken',run_token,'com.holmes.lifecycle/.LifecycleProbe'],stdout=log,stderr=subprocess.STDOUT)
        ok('instrumented real Activity starts',until(10,lambda: phase()[:1]==['ready']))
        first_pid=pid()
        (out/'initial-owner.json').write_text(json.dumps({'pid':first_pid,'phase':phase()},indent=2)+'\n')
        ok('native runner produces a readable initial state',until(10,lambda: field('bands')==300))
        ok('native state changes before recreation',ctl('send seed').startswith('ok bands=301'))
        dimensions=run('shell','wm','size')
        width,height=map(int,re.findall(r'(\d+)x(\d+)',dimensions)[-1])
        startup_ime=run('shell','dumpsys','input_method')
        (out/'cold-start-ime.txt').write_text(startup_ime)
        deadline=time.monotonic()+1.2
        hidden=True
        while time.monotonic()<deadline:
            if field('ime')!=0: hidden=False; break
            time.sleep(.02)
        ok('cold launch keeps IME hidden until an explicit composer tap',
           hidden and 'STATE_HIDDEN|ADJUST_RESIZE' in startup_ime)
        run('shell','input','touchscreen','tap',str(width//3),str(height-63-70))
        ok('first composer tap after cold launch opens the IME within 1.2s',until(1.2,lambda: field('ime')>300))
        run('shell','input','keyevent','BACK')
        ok('Back closes the cold-launch IME within 1.2s',until(1.2,lambda: field('ime')==0))
        for index in range(1,4):
            old_generation=int(phase()[1])
            command('recreate'+str(index))
            recreated=until(5,lambda: phase()[:2]==['recreated',str(old_generation+1)])
            native_ready=recreated and until(2,lambda: field('bands')==301)
            ok('recreation retains the same live native process',native_ready and pid()==first_pid)
            ok('recreation retains the running Lean state',native_ready)
            before=native_text()
            command('stale')
            ok('old Activity callback was delivered by instrumentation',until(2,lambda: phase()[:1]==['stale-delivered']))
            # A completed ping followed by a new command forces a later actual
            # frame/event drain, even if the callback arrived during the prior frame.
            ctl('ping')
            ok('destroyed Activity cannot replace current text',native_text()==before)
            run('shell','input','touchscreen','tap',str(width//3),str(height-63-70))
            ok('first composer tap after recreation opens the IME within 1.2s',until(1.2,lambda: field('ime')>300))
            (out/f'ime-{index}.txt').write_text(run('shell','dumpsys','input_method'))
            run('shell','input','keyevent','BACK')
            ok('Back closes only the IME within 1.2s',until(1.2,lambda: field('ime')==0) and pid()==first_pid)
        command('hold-focus-back')
        ok('focus leaves after the user closed IME',until(2,lambda: phase()[:1]==['focus-held']))
        command('release-focus-back')
        ok('focus returns after user Back',until(2,lambda: phase()[:1]==['focus-released']))
        until_time=time.monotonic()+1.2
        hidden=True
        while time.monotonic()<until_time:
            if field('ime')!=0: hidden=False; break
            time.sleep(.02)
        ok('user Back stays hidden across later window focus',hidden)
        command('hold-focus1')
        ok('real dialog takes Activity window focus',until(2,lambda: phase()[:1]==['focus-held']))
        command('show-pending')
        ok('show is requested while the Activity lacks window focus',until(2,lambda: phase()[:1]==['pending-show']))
        command('release-focus1')
        ok('pending show opens IME when actual window focus returns',until(1.2,lambda: field('ime')>300))
        run('shell','input','keyevent','BACK')
        ok('Back clears pending-focus IME',until(1.2,lambda: field('ime')==0))
        command('hold-focus2')
        ok('second real dialog takes Activity window focus',until(2,lambda: phase()[:1]==['focus-held']))
        command('show-pending')
        ok('second show waits for actual focus',until(2,lambda: phase()[:1]==['pending-show']))
        command('hide-pending')
        ok('hide cancels before actual focus returns',until(2,lambda: phase()[:1]==['pending-hide']))
        command('release-focus2')
        ok('focus returns after pending hide',until(2,lambda: phase()[:1]==['focus-released']))
        until_time=time.monotonic()+1.2
        hidden=True
        while time.monotonic()<until_time:
            if field('ime')!=0: hidden=False; break
            time.sleep(.02)
        ok('canceled show stays hidden after focus returns',hidden)
        command('finish')
        ok('instrumentation requests a real Activity finish',until(2,lambda: phase()[:1]==['finishing']))
        ok('real finish releases the native process and all its workers',until(5,lambda: not pid()))
        transcript=run('logcat','-d')
        ok('native main reports its completed return', 'main returned 0' in transcript)
        ok('native completion skips global exit destructors','FORBIDDEN: process exit ran global destructors' not in transcript)
        app_crashes,external_crashes=crash_lines(transcript,first_pid)
        (out/'external-crashes.txt').write_text('\n'.join(external_crashes)+'\n')
        ok('recreation and finish have no native or Java crash',not app_crashes)
        ok('native destroy observed both configuration and final lifetimes',
           transcript.count('activity destroyed: configuration=1')>=3 and 'activity destroyed: configuration=0' in transcript)
    except AssertionError:
        pass
    finally:
        for name,arguments in [('logcat.txt',('logcat','-d')),('window.txt',('shell','dumpsys','window')),('ime.txt',('shell','dumpsys','input_method')),('ime-service.txt',('shell','dumpsys','activity','services','com.holmes.testime'))]:
            try: (out/name).write_text(run(*arguments,check=False))
            except subprocess.SubprocessError: pass
        run('shell','am','force-stop',PKG,check=False)
        if instrumentation:
            try: instrumentation.wait(timeout=5)
            except subprocess.TimeoutExpired: instrumentation.terminate(); instrumentation.wait(timeout=5)
        if port: run('forward','--remove',f'tcp:{port}',check=False)
        (out/'result.json').write_text(json.dumps({'passed':passed,'failures':failures},indent=2)+'\n')
    print(f'android-lifecycle: {len(passed)} passed, {len(failures)} failed',flush=True)
    return 1 if failures else 0


if __name__=='__main__': raise SystemExit(main())
