#!/usr/bin/env python3
from pathlib import Path
import json,os,socket,subprocess,time
from decode_db import decode,checkpoint_drafts,names
import argparse
parser=argparse.ArgumentParser()
parser.add_argument("--serial",required=True);parser.add_argument("--avd",required=True)
parser.add_argument("--apk",type=Path,required=True);parser.add_argument("--probe",type=Path,required=True)
parser.add_argument("--out",type=Path,required=True)
args=parser.parse_args()
ROOT=Path(__file__).resolve().parent;OUT=args.out.resolve();OUT.mkdir(parents=True,exist_ok=True)
ADB=['/home/holmes/android-sdk/platform-tools/adb','-s',args.serial];PKG='com.holmes.leanquiet'
checks=[];failures=[];port=None;instrumentation=None;alive_before_cleanup=False;token=os.urandom(16).hex()
def run(*args,check=True,timeout=20):
    return subprocess.run(ADB+list(args),check=check,capture_output=True,text=True,timeout=timeout).stdout.strip()
def until(seconds,fn):
    end=time.monotonic()+seconds
    while time.monotonic()<end:
        try:
            result=fn()
            if result:return result
        except (OSError,ValueError,subprocess.SubprocessError):pass
        time.sleep(.025)
    return False
def ok(label,value):
    print(('ok: ' if value else 'FAIL: ')+label,flush=True)
    (checks if value else failures).append(label)
    if not value:raise AssertionError(label)
def phase():
    p=run('shell','run-as',PKG,'cat','files/input-race-state',check=False).split()
    return p[0] if len(p)==3 and p[2]==token else ''
def command(value):
    run('shell','run-as',PKG,'sh','-c',f"'printf %s {value} > files/input-race-command.next && mv files/input-race-command.next files/input-race-command'")
def ctl(value,timeout=2):
    with socket.create_connection(('127.0.0.1',port),timeout=timeout) as s:
        s.sendall((value+'\n').encode());return s.makefile(encoding='utf-8').readline().strip()
def committed(text):
    v=ctl('visible');(OUT/'latest-visible.txt').write_text(v+'\n')
    return text in v and '(pending)' not in v
try:
    ok('owned AVD identity is exact',run('emu','avd','name').splitlines()[0]==args.avd)
    ok('owned emulator boot completes',until(120,lambda:run('shell','getprop','sys.boot_completed')=='1'))
    run('shell','wm','dismiss-keyguard');run('shell','svc','power','stayon','true')
    run('shell','am','force-stop',PKG);run('install','-r',str(args.apk.resolve()),timeout=90)
    run('install','-r',str(args.probe.resolve()),timeout=60);run('shell','pm','clear',PKG)
    run('shell','am','wait-for-broadcast-idle','--flush-broadcast-loopers',timeout=30)
    run('logcat','-c');port=int(run('forward','tcp:0','localabstract:leanquiet'))
    log=(OUT/'instrumentation.log').open('w')
    instrumentation=subprocess.Popen(ADB+['shell','am','instrument','-w','-e','runToken',token,'com.holmes.ownedinput/.OwnedInputProbe'],stdout=log,stderr=subprocess.STDOUT)
    ok('real Activity and pump symbols attach',until(15,lambda:phase()=='ready'))
    ok('actual Main control loop answers',until(20,lambda:ctl('ping')=='pong'))
    (OUT/'pid.txt').write_text(run('shell','pidof',PKG)+'\n')
    (OUT/'setup.txt').write_text(ctl('found Input Race|Alice',60)+'\n'+ctl('wait',60)+'\n'+ctl('channel',30)+'\n')
    command('control');ok('actual native pump gate precedes real ordered callbacks',until(3,lambda:phase()=='control-queued'))
    (OUT/'control-enqueued.txt').write_text(run('shell','run-as',PKG,'cat','files/control-enqueued.txt')+'\n')
    ok('held pump prevents ordered send from reaching App', 'control_A_20261031' not in ctl('visible'))
    command('release-control');ok('ordered control pump resumes',until(2,lambda:phase()=='release-control'))
    ok('real ordered Send commits A within original five-second observation bound',until(5,lambda:committed('control_A_20261031')))
    ctl('wait',60)
    command('race');ok('real TEXT(A),SEND,TEXT(B) callbacks finish while original pump held',until(3,lambda:phase()=='race-queued'))
    (OUT/'race-enqueued.txt').write_text(run('shell','run-as',PKG,'cat','files/race-enqueued.txt')+'\n')
    ok('held pump prevents either race text from reaching App','race_' not in ctl('visible'))
    command('release-race');ok('race pump resumes',until(2,lambda:phase()=='release-race'))
    ok('repaired real Send commits captured A within five-second diagnostic bound',until(5,lambda:committed('race_A_20261031')))
    visible=ctl('visible');(OUT/'visible.txt').write_text(visible+'\n')
    ok('newer B is not incorrectly committed','race_B_20261031' not in visible)
    state=ctl('state');(OUT/'app-state.txt').write_text(state+'\n')
    ok('newer B remains the actual App draft','text \"race_B_20261031\"' in state)
    expected=['control_A_20261031','race_A_20261031']
    absent=['race_B_20261031']
    capture_serial=[0]
    def capture(name):
        capture_serial[0]+=1;name=name+'-'+str(capture_serial[0])
        command('capture-'+name);ok(name+' native capture completes',until(2,lambda:phase()=='capture-'+name))
        value=run('shell','run-as',PKG,'cat','files/capture-'+name+'.txt')
        (OUT/(name+'-editor.txt')).write_text(value+'\n');return value
    for name in ['hardware','busy','lateclear','touch']:
        ctl('wait',60);command(name)
        if name=='touch':
            def observed_down():
                reply=ctl('input')
                (OUT/'touch-down-input.txt').write_text(reply+'\n')
                return 'press true' in reply
            ok('real native Down reaches actual App press before holding Up',until(3,observed_down))
        queued=name+('-released' if name=='lateclear' else '-queued')
        produced=until(4,lambda:phase()==queued)
        if name=='touch' and produced:
            gesture=run('shell','run-as',PKG,'cat','files/touch-gesture.txt')
            (OUT/'touch-gesture.txt').write_text(gesture+'\n')
            values=dict(line.split('=',1) for line in gesture.splitlines())
            produced=values.get('observed')=='true' and int(values['pending-ticket'])>0 and 0<=int(values['elapsed'])<500
        ok(name+' actual producer phase completes',produced)
        if name!='lateclear':
            command('release-'+name);ok(name+' actual pump resumes',until(2,lambda:phase()=='release-'+name))
        ok(name+' captured A commits within unchanged five-second observation bound',until(5,lambda:committed(name+'_A')))
        expected.append(name+'_A');absent.append(name+'_B')
        value=capture(name+'-after')
        if name in ['busy','lateclear','touch']:
            ok(name+' newer Java draft B survives','editor='+name+'_B\n' in value)
            ok(name+' newer App draft B survives',until(3,lambda:'text "'+name+'_B"' in ctl('state')))
        else:ok('physical Enter clears exactly once without fallback newline','editor=\n' in value)
        ok(name+' async clear slot is reusable',until(2,lambda:'clear=0' in capture(name+'-clear')))
    # The same actual send-button coordinates just committed touch_A. Its long
    # gesture must not activate Send, and its terminal candidate must retire.
    command('long');ok('actual held touch completes',until(3,lambda:phase()=='long-queued'))
    ctl('wait',60);ok('held Send button never commits an unowned latest draft','long_A' not in ctl('visible'))
    ok('held Send button preserves the actual App draft',until(3,lambda:'text "long_A"' in ctl('state')))
    absent.append('long_A');capture('long-after')
    command('stale');ok('old-editor action admitted before navigation',until(3,lambda:phase()=='stale-queued'))
    oldowner=run('shell','run-as',PKG,'cat','files/stale-queued.txt').split('owner=')[1].splitlines()[0]
    ctl('back');ctl('channel');newer=capture('stale-new-owner')
    ok('actual navigation replaces semantic editor owner','owner='+oldowner+'\n' not in newer)
    command('release-stale');ok('stale action pump resumes',until(2,lambda:phase()=='release-stale'))
    ctl('wait',60);time.sleep(.2);ok('stale action cannot submit in replacement editor','stale_A' not in ctl('visible'))
    absent.append('stale_A')
    command('geometry');ok('geometry action admitted before resize',until(3,lambda:phase()=='geometry-queued'))
    oldowner=run('shell','run-as',PKG,'cat','files/geometry-queued.txt').split('owner=')[1].splitlines()[0]
    oldgen=ctl('input').split('generation ')[1]
    run('shell','wm','size','1080x2300')
    ok('actual OS viewport changed while its old observed snapshot is held',until(3,lambda:'1080x2300' in run('shell','wm','size')))
    ok('App has not applied held viewport before terminal delivery',ctl('input').split('generation ')[1]==oldgen)
    resized=capture('geometry-same-owner')
    ok('geometry does not replace semantic editor owner','owner='+oldowner+'\n' in resized)
    command('release-geometry');ok('geometry pump resumes',until(2,lambda:phase()=='release-geometry'))
    ok('owned Send survives geometry-only lease change in its actual delivery turn',until(5,lambda:committed('geometry_A')))
    ok('delivery turn also applied actual changed viewport',ctl('input').split('generation ')[1]!=oldgen)
    expected.append('geometry_A');run('shell','wm','size','reset')
    def checkpoint_copy(name):
        dest=OUT/name;dest.mkdir(exist_ok=True)
        for item in ['quiet.db','quiet.db-wal','quiet.db-shm']:
            data=subprocess.run(ADB+['exec-out','run-as',PKG,'cat','files/'+item],capture_output=True,timeout=10)
            if data.returncode==0:(dest/item).write_bytes(data.stdout)
            elif item=='quiet.db':raise RuntimeError('checkpoint database copy failed')
        result=checkpoint_drafts(dest/'quiet.db')
        if result is not None:(dest/'checkpoint.json').write_text(json.dumps(result,indent=2)+'\n')
        return result
    for name,newer in [('holdclear',False),('holdclearnewer',True)]:
        ctl('wait',60);command(name)
        ok(name+' original clear callback retained without blocking UI',until(4,lambda:phase()==name+'-held'))
        ok(name+' accepted A commits while callback is held',until(5,lambda:committed(name+'_A')))
        expected.append(name+'_A');absent.append(name+'_B')
        if newer:
            command('type-'+name+'_B');ok('later B arrives before actual background',until(2,lambda:phase()=='type-'+name+'_B'))
        before=capture(name+'-before-background')
        want=name+'_B' if newer else ''
        ok(name+' native callback really has not cleared the editor','editor='+name+('_B' if newer else '_A')+'\n' in before)
        pid=run('shell','pidof',PKG)
        run('shell','input','keyevent','KEYCODE_HOME');command('await-paused')
        ok(name+' actual Android Activity pauses',until(3,lambda:phase()=='await-paused'))
        def saved():
            try:
                value=checkpoint_copy(name+'-background-store')
                return value and any(d['acceptance']==value['current'] and d['text']==want for d in value['drafts'])
            except (AssertionError,ValueError,IndexError,subprocess.SubprocessError):return False
        ok(name+' actual SQLite checkpoint preserves only unconsumed draft',until(5,saved))
        run('shell','am','start','-n',PKG+'/.LeanActivity');command('await-resumed')
        ok(name+' actual Activity resumes with installed editor',until(5,lambda:phase()=='await-resumed'))
        command('recreate');ok(name+' real Activity recreation finishes',until(6,lambda:phase()=='recreate'))
        ok(name+' recreation retains the same Lean process',run('shell','pidof',PKG)==pid)
        ok(name+' App draft survives suspension/recreation correctly',until(3,lambda:'text "'+want+'"' in ctl('state')))
        restored=capture(name+'-restored')
        ok(name+' actual replacement Field contains only unconsumed draft','editor='+want+'\n' in restored)
        command('release-clear');ok(name+' old callback eventually executes',until(2,lambda:phase()=='release-clear'))
        late=capture(name+'-late-clear')
        ok(name+' late callback cannot erase replacement draft','editor='+want+'\n' in late)
    # Same semantic draft, a new mount owner, and typing after the replacement
    # command was issued. The actual Java callback is delayed, not substituted.
    command('type-handoff_B');ok('handoff starts with actual B',until(2,lambda:phase()=='type-handoff_B'))
    ok('App observes initial handoff B',until(3,lambda:'text "handoff_B"' in ctl('state')))
    command('hold-install');ok('install callback barrier enabled',until(2,lambda:phase()=='hold-install'))
    run('shell','input','keyevent','KEYCODE_HOME');command('await-paused')
    ok('handoff actual Activity pauses',until(3,lambda:phase()=='await-paused'))
    time.sleep(.3);run('shell','am','start','-n',PKG+'/.LeanActivity');command('await-install')
    ok('actual same-editor install is retained',until(4,lambda:phase()=='await-install'))
    command('hold-latest-copy');ok('App latest reads cannot refresh the retained installation',until(2,lambda:phase()=='hold-latest-copy'))
    command('type-handoff_C');ok('newer C arrives while install is delayed',until(2,lambda:phase()=='type-handoff_C'))
    command('release-install');ok('actual install callback resumes',until(2,lambda:phase()=='release-install'))
    command('await-latest-fault');ok('delayed handoff actually overlaps failed latest reads',until(3,lambda:phase()=='await-latest-fault'))
    handoff=capture('handoff-final');ok('same-editor handoff preserves actual Field C','editor=handoff_C\n' in handoff)
    command('recover-copy');ok('handoff latest reads recover',until(2,lambda:phase()=='recover-copy'))
    ok('same-editor handoff cannot overwrite newer App C',until(3,lambda:'text "handoff_C"' in ctl('state')))
    absent.extend(['handoff_B','handoff_C'])
    # Force the original JNI copy sites: neither may turn missing memory into
    # a valid empty draft/action. The second case combines a stale content
    # revision with a failed refresh and a real newly prepared photo.
    ctl('photo');ok('snapshot-fault fixture has an actual prepared photo',until(3,lambda:'photos 1 ' in ctl('photo-status')))
    command('snapshotfault');ok('text-and-photo action admitted before read failure',until(3,lambda:phase()=='snapshotfault-queued'))
    command('release-snapshotfault');ok('snapshot-fault pump resumes',until(2,lambda:phase()=='release-snapshotfault'))
    command('await-snapshot-fault');ok('actual immutable snapshot allocation failed',until(3,lambda:phase()=='await-snapshot-fault'))
    command('await-refused');ok('actual App explicitly refuses unreadable captured action',until(3,lambda:phase()=='await-refused'))
    ok('failed snapshot cannot become a photo-only empty message','snapshotfault_A' not in ctl('visible'))
    snap=capture('snapshotfault-refused')
    ok('failed snapshot preserves native text','editor=snapshotfault_A\n' in snap)
    ok('failed snapshot preserves prepared photo','photos 1 ' in ctl('photo-status'))
    command('recover-copy');ok('allocation failure injection stops',until(2,lambda:phase()=='recover-copy'))
    command('resend');ok('same text-and-photo can be retried',until(2,lambda:phase()=='resend'))
    ok('recovered snapshot slot commits exact original text',until(5,lambda:committed('snapshotfault_A')))
    expected.append('snapshotfault_A');absent.append('')
    command('type-content_seed');ok('known draft exists before latest-copy failure',until(2,lambda:phase()=='type-content_seed'))
    ok('actual App observed known nonempty draft',until(3,lambda:'text "content_seed"' in ctl('state')))
    command('contentfault');ok('content action owns A before newer B and read fault',until(3,lambda:phase()=='contentfault-queued'))
    command('await-latest-fault');ok('actual latest-draft allocation fails repeatedly',until(3,lambda:phase()=='await-latest-fault'))
    ctl('photo');ok('actual photo set changes while refresh cannot advance content version',until(3,lambda:'photos 1 ' in ctl('photo-status')))
    command('release-contentfault');ok('content-fault pump resumes',until(2,lambda:phase()=='release-contentfault'))
    command('await-refused');ok('actual App explicitly refuses stale content despite latest-read failure',until(3,lambda:phase()=='await-refused'))
    ok('pure current-content guard refuses action with changed photo set','contentfault_A' not in ctl('visible'))
    ok('failed owned latest read cannot erase known App draft','text ""' not in ctl('state'))
    draft=capture('contentfault-refused');ok('latest-copy failure preserves actual newer Field B','editor=contentfault_B\n' in draft)
    command('recover-copy');ok('latest-copy allocation recovers',until(2,lambda:phase()=='recover-copy'))
    ok('App adopts exact newer B after allocation recovers',until(3,lambda:'text "contentfault_B"' in ctl('state')))
    command('resend');ok('new action explicitly selects current photo set',until(2,lambda:phase()=='resend'))
    ok('current text and photo commit after explicit retry',until(5,lambda:committed('contentfault_B')))
    expected.append('contentfault_B');absent.extend(['contentfault_A','content_seed'])
    command('type-ready_saved');ok('saved draft prepared before ownerless replacement',until(2,lambda:phase()=='type-ready_saved'))
    ok('App observed saved draft',until(3,lambda:'text "ready_saved"' in ctl('state')))
    command('recreate-uninstalled-first');ok('actual new Field rejects typing before ownership installation',until(6,lambda:phase()=='recreate-uninstalled-first'))
    command('focus-tap-first');ok('first real current-frame field tap retains explicit pending focus',until(4,lambda:phase()=='focus-tap-first'))
    ok('ownerless typing cannot change saved App draft','text "ready_saved"' in ctl('state'))
    command('release-install');ok('authoritative field installation resumes',until(2,lambda:phase()=='release-install'))
    command('focus-ready');ok('first tap gains enabled InputConnection and focus after install',until(4,lambda:phase()=='focus-ready'))
    ok('first tap actually opens the Android IME after installation',until(3,lambda:int(ctl('state').split(' ime ')[1].split()[0])>0))
    ready=capture('ready-installed');ok('atomic installation restores exact saved text','editor=ready_saved\n' in ready)
    command('hide-ime');ok('real hide cancels focus',until(2,lambda:phase()=='hide-ime'))
    command('recreate-uninstalled-cancel');ok('second ownerless interval rejects typing',until(6,lambda:phase()=='recreate-uninstalled-cancel'))
    command('focus-tap-cancel');ok('second field tap owns a pending focus request',until(4,lambda:phase()=='focus-tap-cancel'))
    command('hide-ime');ok('hide cancels before installation',until(2,lambda:phase()=='hide-ime'))
    command('release-install');ok('cancelled-focus installation resumes',until(2,lambda:phase()=='release-install'))
    command('focus-cancelled');ok('installation cannot resurrect cancelled focus',until(4,lambda:phase()=='focus-cancelled'))
    ctl('back');command('home');ok('real hardware Enter is admitted on actual Home',until(3,lambda:phase()=='home-queued'))
    command('release-home');ok('Home action reaches actual App',until(2,lambda:phase()=='release-home'))
    command('await-refused');ok('Home explicitly refuses hidden-composer submission',until(3,lambda:phase()=='await-refused'))
    ctl('channel');ok('Home refusal preserves saved conversation draft',until(3,lambda:'text "ready_saved"' in ctl('state')))
    absent.extend(['home_A','ready_saved'])
    command('clearthrow');ok('actual clear-post exception action is admitted',until(3,lambda:phase()=='clearthrow'))
    ok('clear-post failure does not undo the accepted exact A commit',until(5,lambda:committed('clearthrow_A')))
    command('repeat-consumed');ok('actual JNI cleanup refuses a second send of consumed raw A',until(3,lambda:phase()=='repeat-consumed'))
    ok('clear-post failure leaves logical App draft consumed',until(3,lambda:'text ""' in ctl('state')))
    command('type-clearthrow_B');ok('new typing advances revision after refused replay',until(2,lambda:phase()=='type-clearthrow_B'))
    command('resend');ok('new revision can submit after failed clear callback',until(2,lambda:phase()=='resend'))
    ok('new revision commits exact B and slot recovers',until(5,lambda:committed('clearthrow_B')))
    expected.extend(['clearthrow_A','clearthrow_B'])
    ctl('open create')
    command('community');ok('Continue captures original community field before newer typing',until(3,lambda:phase()=='community-queued'))
    command('release-community');ok('community Continue reaches actual App',until(2,lambda:phase()=='release-community'))
    ok('captured community Continue opens actual name editor',until(3,lambda:'PageId.createName' in ctl('input')))
    command('profile');ok('physical Enter captures original profile before newer typing',until(3,lambda:phase()=='profile-queued'))
    command('release-profile');ok('profile Continue reaches actual App',until(2,lambda:phase()=='release-profile'))
    ok('actual created community has captured A name',until(5,lambda:'community_A*' in ctl('comms')))
    ok('later B did not name the new community','community_B' not in ctl('comms'))
    ctl('wait',60);ctl('channel')
    command('createdpost');ok('new community has a usable owned composer',until(3,lambda:phase()=='createdpost-queued'))
    command('release-createdpost');ok('new community send reaches actual App',until(2,lambda:phase()=='release-createdpost'))
    ok('actual new community accepts captured message once',until(5,lambda:committed('createdpost_A')))
    expected.append('createdpost_A');absent.append('createdpost_B')
    ctl('wait',60);command('done');ok('instrumentation completes',until(2,lambda:phase()=='done'))
    alive_before_cleanup=run('shell','pidof',PKG)==(OUT/'pid.txt').read_text().strip()
    run('shell','am','force-stop',PKG)
    for name in ['quiet.db','quiet.db-wal','quiet.db-shm']:
        cp=subprocess.run(ADB+['exec-out','run-as',PKG,'cat','files/'+name],capture_output=True,timeout=15)
        if cp.returncode==0:(OUT/name).write_bytes(cp.stdout)
        elif name=='quiet.db':raise RuntimeError('actual SQLite copy failed')
    evidence=decode(OUT/'quiet.db');(OUT/'sqlite-evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
    name_facts=names(OUT/'quiet.db');(OUT/'sqlite-name-evidence.json').write_text(json.dumps(name_facts,indent=2)+'\n')
    created=[r for r in name_facts if r['kind']=='named' and r['value']=='community_A']
    ok('SQLite actual valid named fact contains captured community A exactly once',len(created)==1)
    profiles=[r for r in name_facts if r['community']==created[0]['community'] and r['kind']=='profile']
    ok('SQLite actual valid profile contains captured profile A exactly once',sum(r['value']=='profile_A' for r in profiles)==1)
    ok('SQLite excludes both later Continue field values',all(r['value'] not in ['community_B','profile_B'] for r in name_facts))
    ok('authenticated captured post belongs to the actually created community',any(r['plaintext']=='createdpost_A' and r['community']==created[0]['community'] for r in evidence))
    texts=[r['plaintext'] for r in evidence]
    ok('SQLite authenticated valid message is exactly ordered A once',texts.count('control_A_20261031')==1)
    ok('SQLite authenticated valid message is exactly captured A once',texts.count('race_A_20261031')==1)
    ok('SQLite contains no incorrectly committed later B',texts.count('race_B_20261031')==0)
    for text in expected:ok('SQLite authenticated exact accepted action once: '+text,texts.count(text)==1)
    for text in absent:ok('SQLite excludes refused/unowned/newer text: '+text,texts.count(text)==0)
except Exception as e:
    if not failures:failures.append(str(e))
    print('ERROR: '+repr(e),flush=True)
finally:
    alive_before_cleanup=alive_before_cleanup or ((OUT/'pid.txt').exists() and run('shell','pidof',PKG,check=False)==(OUT/'pid.txt').read_text().strip())
    if failures and port:
        for name in ['state','input','photo-status','reader']:
            try:(OUT/(name+'-at-failure.txt')).write_text(ctl(name)+'\n')
            except (OSError,ValueError,subprocess.SubprocessError):pass
    for name,args in [('logcat.txt',('logcat','-d')),('activities.txt',('shell','dumpsys','activity','activities'))]:
        try:(OUT/name).write_text(run(*args,check=False))
        except subprocess.SubprocessError:pass
    try:(OUT/'final.png').write_bytes(subprocess.check_output(ADB+['exec-out','screencap','-p'],timeout=10))
    except subprocess.SubprocessError:pass
    run('shell','wm','size','reset',check=False)
    run('shell','am','force-stop',PKG,check=False)
    if failures:
        failed_store=OUT/'failed-store';failed_store.mkdir(exist_ok=True)
        for name in ['quiet.db','quiet.db-wal','quiet.db-shm']:
            data=subprocess.run(ADB+['exec-out','run-as',PKG,'cat','files/'+name],capture_output=True,timeout=10)
            if data.returncode==0:(failed_store/name).write_bytes(data.stdout)
        try:
            (failed_store/'sqlite-evidence.json').write_text(json.dumps(decode(failed_store/'quiet.db'),indent=2)+'\n')
        except Exception as error:(failed_store/'decode-error.txt').write_text(repr(error)+'\n')
    if instrumentation:
        try:instrumentation.wait(timeout=5)
        except subprocess.TimeoutExpired:instrumentation.terminate();instrumentation.wait(timeout=5)
    if port:run('forward','--remove',f'tcp:{port}',check=False)
    (OUT/'result.json').write_text(json.dumps({'classification':'owned-input-first-semantic-regression' if not failures else 'diagnostic-incomplete','passed':checks,'failures':failures,'process_alive_before_cleanup':alive_before_cleanup},indent=2)+'\n')
print(f'input race diagnostic: {len(checks)} passed, {len(failures)} failed',flush=True)
raise SystemExit(bool(failures))
