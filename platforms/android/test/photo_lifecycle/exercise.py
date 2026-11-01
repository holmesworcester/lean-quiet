#!/usr/bin/env python3
"""Actual Main/SQLite, Android picker, gated real photo executor and recreation."""
from pathlib import Path
import argparse,json,os,re,socket,subprocess,time
import xml.etree.ElementTree as ET

ROOT=Path(__file__).resolve().parents[4]
PKG='com.holmes.leanquiet'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--serial',required=True)
    parser.add_argument('--apk',required=True,type=Path)
    parser.add_argument('--out',required=True,type=Path)
    args=parser.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    adb=[str(Path(os.environ.get('ANDROID_SDK',Path.home()/'android-sdk'))/'platform-tools/adb'),'-s',args.serial]
    passed=[];failures=[];port=None;instrumentation=None;token=os.urandom(16).hex()

    def run(*arguments,check=True,timeout=20):
        return subprocess.run(adb+list(arguments),capture_output=True,text=True,check=check,timeout=timeout).stdout.strip()

    def until(seconds,predicate):
        deadline=time.monotonic()+seconds
        while time.monotonic()<deadline:
            try:
                result=predicate()
                if result:return result
            except (OSError,ValueError,subprocess.SubprocessError):pass
            time.sleep(.05)
        return False

    def ok(label,value):
        if value:passed.append(label);print('ok: '+label,flush=True)
        else:failures.append(label);print('FAIL: '+label,flush=True);raise AssertionError(label)

    def phase():
        observed=run('shell','run-as',PKG,'cat','files/photo-lifecycle-state',check=False).split()
        return observed[:3] if len(observed)==4 and observed[3]==token else []

    def command(value):
        run('shell','run-as',PKG,'sh','-c',f"'printf %s {value} > files/photo-lifecycle-command.next && mv files/photo-lifecycle-command.next files/photo-lifecycle-command'")

    def ctl(command,timeout=.5):
        with socket.create_connection(('127.0.0.1',port),timeout=timeout) as stream:
            stream.sendall((command+'\n').encode())
            return stream.makefile(encoding='utf-8').readline().strip()

    def photos(count,pending):
        return ctl('photo-status').startswith(f'photos {count} pending {str(pending).lower()}')

    def ui():
        run('shell','uiautomator','dump','/sdcard/photo-lifecycle-ui.xml')
        text=run('shell','cat','/sdcard/photo-lifecycle-ui.xml')
        (out/'picker.xml').write_text(text)
        return list(ET.fromstring(text).iter('node'))

    def picker():
        return any('photopicker' in n.attrib.get('package','') or n.attrib.get('resource-id','').endswith('/privacy_text') or n.attrib.get('content-desc')=='Photos' for n in ui())

    def click(node):
        x0,y0,x1,y1=map(int,re.findall(r'\d+',node.attrib['bounds']))
        run('shell','input','tap',str((x0+x1)//2),str((y0+y1)//2))

    def select():
        nodes=ui()
        candidates=[n for n in nodes if n.attrib.get('resource-id','').endswith('/icon_thumbnail')]
        if not candidates:candidates=[n for n in nodes if n.attrib.get('resource-id','').endswith('/image') and n.attrib.get('content-desc')]
        if not candidates:candidates=[n for n in nodes if n.attrib.get('content-desc','').startswith('Photo taken on')]
        if candidates:click(candidates[0]);return True
        return False

    def choose_real_photo():
        ok('real system picker exposes the seeded photograph',until(15,select))
        for node in ui():
            if node.attrib.get('text') in ['Add','Open','Done'] and node.attrib.get('enabled')=='true':click(node);break

    def recreate(index,picker_open=False):
        before=int(phase()[1]);command('recreate'+str(index))
        if picker_open:
            ok('picker owner is destroyed before system result returns',until(5,lambda:phase()[:1] in [['owner-destroyed'],['recreated']]))
            run('shell','input','keyevent','BACK')
        ok('actual Activity replacement completes',until(5,lambda:phase()[:2]==['recreated',str(before+1)]))
        ok('photo recreation retains the native process',run('shell','pidof',PKG,check=False)==first_pid)

    try:
        run('shell','am','force-stop',PKG)
        run('install','-r',str(args.apk.resolve()),timeout=60)
        run('install','-r',str(ROOT/'out/photo-lifecycle-probe.apk'),timeout=60)
        # This fixture owns and verifies its emulator; clear only its app data.
        run('shell','pm','clear',PKG)
        run('shell','am','wait-for-broadcast-idle','--flush-broadcast-loopers',timeout=30)
        run('logcat','-c')
        port=int(run('forward','tcp:0','localabstract:leanquiet'))
        log=(out/'instrumentation.log').open('w')
        instrumentation=subprocess.Popen(adb+['shell','am','instrument','-w','-e','runToken',token,'com.holmes.photolifecycle/.PhotoLifecycleProbe'],stdout=log,stderr=subprocess.STDOUT)
        ok('real Main instrumentation starts',until(15,lambda:phase()[:1]==['ready']))
        first_pid=run('shell','pidof',PKG)
        (out/'owner.json').write_text(json.dumps({'pid':first_pid,'phase':phase()},indent=2)+'\n')
        ok('actual native Main control loop answers',until(20,lambda:ctl('ping')=='pong'))
        ctl('found Photo lifetime|Ann',60);ctl('wait',60)
        # A navigation command replies before its first frame is published.
        # Observe a newly retained chat frame before starting photo timings;
        # cold native rendering is setup, not a 0.5-second photo-status bound.
        previous=re.search(r' serial (\d+) ',ctl('input',30))
        assert previous is not None,'missing pre-navigation input serial'
        ctl('channel',30)
        deadline=time.monotonic()+30
        published=False
        while time.monotonic()<deadline:
            snapshot=ctl('input',max(.001,deadline-time.monotonic()))
            match=re.search(r'^page App\.PageId\.chat serial (\d+) retained \[(\d+)',snapshot)
            if match and match[1]!=previous[1] and match[1]==match[2]:
                (out/'chat-ready.txt').write_text(snapshot+'\n')
                published=True;break
        ok('actual chat publication is ready before photo measurements',published)
        ok('new composer starts with no pending photo',photos(0,False))
        ctl('pick-photo');ok('ordinary picker really pauses the app',until(15,picker))
        choose_real_photo()
        ok('ordinary picker pause still yields one decoded photo',until(15,lambda:photos(1,False)))
        result=ctl('photo-status')
        ok('ordinary system decode retains bounded EXIF orientation','(1024, 2048)' in result)
        ctl('post Photo before recreation',30);ctl('wait',60)
        ok('ordinary selected photo can be sent',until(5,lambda:photos(0,False)))

        ctl('pick-photo');ok('picker is open before recreation',until(15,picker))
        recreate(1,picker_open=True)
        ok('recreated picker clears App pending request',until(3,lambda:photos(0,False)))

        command('gate-decode');ok('actual photo executor is held before decoding',until(2,lambda:phase()[:1]==['decode-gated']))
        ctl('pick-photo');ok('real picker opens with executor busy',until(15,picker))
        choose_real_photo()
        ok('real selected photo remains pending behind executor gate',until(3,lambda:photos(0,True)))
        recreate(2)
        ok('recreation cancels queued decoder request',until(3,lambda:photos(0,False)))
        command('release-decode');ok('old actual worker gate is released',until(2,lambda:phase()[:1]==['decode-released']))

        ctl('pick-photo');ok('replacement can start another actual picker',until(15,picker))
        command('stale-photo');ok('old-instance matching-token callback was delivered',until(2,lambda:phase()[:1]==['stale-photo-delivered']))
        run('shell','input','keyevent','BACK')
        ok('retired Activity cannot complete replacement photo request',until(3,lambda:photos(0,False)))
        ctl('ping');ok('no stale photo appears on a later real frame',photos(0,False))
        command('done');ok('instrumentation finishes its bounded command run',until(2,lambda:phase()[:1]==['done']))
    except AssertionError:pass
    finally:
        for name,arguments in [('logcat.txt',('logcat','-d')),('activities.txt',('shell','dumpsys','activity','activities')),('window.txt',('shell','dumpsys','window'))]:
            try:(out/name).write_text(run(*arguments,check=False))
            except subprocess.SubprocessError:pass
        try:(out/'final.png').write_bytes(subprocess.check_output(adb+['exec-out','screencap','-p'],timeout=10))
        except subprocess.SubprocessError:pass
        run('shell','am','force-stop',PKG,check=False)
        if instrumentation:
            try:instrumentation.wait(timeout=5)
            except subprocess.TimeoutExpired:instrumentation.terminate();instrumentation.wait(timeout=5)
        if port:run('forward','--remove',f'tcp:{port}',check=False)
        (out/'result.json').write_text(json.dumps({'passed':passed,'failures':failures},indent=2)+'\n')
    print(f'android photo lifecycle: {len(passed)} passed, {len(failures)} failed',flush=True)
    return 1 if failures else 0

if __name__=='__main__':raise SystemExit(main())
