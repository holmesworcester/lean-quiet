#!/usr/bin/env python3
"""Build isolated actual Android mutations; require their precise UI assertion.

Process exit at explicit Activity.finish is expected. A native crash, Java
exception, build failure or fixture infrastructure failure is never a kill.
"""
from pathlib import Path
import argparse, difflib, hashlib, json, os, shutil, subprocess, sys, tempfile
from crashes import crash_lines
ROOT=Path(__file__).resolve().parents[4]
C='platforms/android/twin/activity.c'
J='platforms/android/twin/java/com/holmes/leanquiet/LeanActivity.java'
D='platforms/headless/TwinDemo.lean'
CASES=[
 ('configuration-closes',C,'if (!recreate) ba_closing = true;','ba_closing = true;',
  'recreation retains the same live native process'),
 ('stale-activity',C,'return ba_act && (*env)->IsSameObject(env, activity, ba_act);','return true;',
  'destroyed Activity cannot replace current text'),
 ('global-exit',C,'  _Exit(code);','  exit(code);',
  'native completion skips global exit destructors'),
 ('drop-unfocused-show',J,'if (!hasWindowFocus() || !edit.isAttachedToWindow()) return;',
  'if (!hasWindowFocus() || !edit.isAttachedToWindow()) { imeWanted = false; return; }',
  'pending show opens IME when actual window focus returns'),
 ('ignore-pending-hide',J,'      imeWanted = show;','      if (show) imeWanted = true;',
  'canceled show stays hidden after focus returns'),
 ('forget-user-hide',J,'    if (imeWasVisible && !visible) imeWanted = false;',
  '    if (imeWasVisible && !visible) { /* broken: retain dismissed request */ }',
  'user Back stays hidden across later window focus'),
 ('automatic-editor-show',J,
  '    getWindow().setSoftInputMode(android.view.WindowManager.LayoutParams.SOFT_INPUT_STATE_HIDDEN\n        | android.view.WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE);\n', '',
  'cold launch keeps IME hidden until an explicit composer tap'),
 ('forget-legacy-reinstall',D,'    | .surface true => discard <| Platform.editor 4 0 0 ""\n','',
  'first composer tap after recreation opens the IME within 1.2s'),
]


def exercise(serial,apk,out,expected=None):
    out.mkdir(parents=True,exist_ok=True)
    result=subprocess.run([sys.executable,str(ROOT/'platforms/android/test/lifecycle/exercise.py'),
       '--serial',serial,'--apk',str(apk),'--out',str(out),'--ime-prepared'],cwd=ROOT,
       capture_output=True,text=True,timeout=150)
    text=result.stdout+result.stderr
    (out/'driver.log').write_text(text)
    print(text,end='',flush=True)
    assert result.returncode>=0,'host driver terminated by signal'
    assert 'Traceback' not in text,'fixture exception is not a control result'
    report=json.loads((out/'result.json').read_text())
    log=(out/'logcat.txt').read_text()
    owner=json.loads((out/'initial-owner.json').read_text())
    target_crashes,external_crashes=crash_lines(log,owner['pid'])
    (out/'external-crashes.txt').write_text('\n'.join(external_crashes)+'\n')
    assert not target_crashes, 'target native/Java crash is not a valid control'
    if expected is None:
        assert result.returncode==0 and not report['failures'], 'positive lifecycle fixture failed'
    else:
        assert result.returncode==1 and report['failures']==[expected], (expected,report['failures'])
        print('refused: '+out.name+' (compiled; exact actual UI assertion)',flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--serial',required=True)
    parser.add_argument('--out',type=Path,default=ROOT/'out/lifecycle')
    parser.add_argument('--cases',help='comma separated diagnostic subset; CI runs all eight')
    args=parser.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    cases={c[0] for c in CASES} if not args.cases else set(args.cases.split(','))
    assert cases and cases<={c[0] for c in CASES}
    # Mutants change the app, never the keyboard service. Install the service
    # once after explicitly unbinding any prior selected version; repeated APK
    # replacement otherwise leaves IMMS believing a dead service is connected.
    adb=[str(Path(os.environ.get('ANDROID_SDK',Path.home()/'android-sdk'))/'platform-tools/adb'),'-s',args.serial]
    with (out/'ime-suite-setup.log').open('w') as log:
        for arguments in [['shell','ime','reset'],['install','-r',str(ROOT/'out/testime.apk')],
                          ['shell','am','wait-for-broadcast-idle','--flush-broadcast-loopers']]:
            subprocess.run(adb+arguments,stdout=log,stderr=subprocess.STDOUT,timeout=60,check=True)
    exercise(args.serial,ROOT/'out/lifecycle.apk',out/'baseline')
    with tempfile.TemporaryDirectory(prefix='android-lifecycle-negative-',dir=os.environ['TMPDIR']) as tmp:
        scratch=Path(tmp)
        shutil.copytree(ROOT,scratch,dirs_exist_ok=True,
            ignore=shutil.ignore_patterns('.git','.lake','out','target','__pycache__'))
        subprocess.run(['cp','-a','--reflink=auto',str(ROOT/'.lake'),str(scratch)],check=True)
        (scratch/'out').mkdir()
        for name in ['leanrt','cache','stdc']:
            subprocess.run(['cp','-a','--reflink=auto',str(ROOT/'out'/name),str(scratch/'out')],check=True)
        originals={f:(scratch/f).read_text() for f in [C,J,D]}
        for name,file,old,new,expected in CASES:
            if name not in cases:continue
            for path,source in originals.items():(scratch/path).write_text(source)
            source=originals[file]
            assert source.count(old)==1,(name,'mutation anchor missing/ambiguous')
            (scratch/file).write_text(source.replace(old,new))
            case=out/name;case.mkdir(exist_ok=True)
            (case/'source.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),source.replace(old,new).splitlines(True),fromfile=file,tofile=file)))
            apk=case/'mutant.apk'
            with (case/'build.log').open('w') as log:
                subprocess.run(['systemd-run','--user','--scope','-p','MemoryMax=48G','-p','MemorySwapMax=0',
                    'bash','platforms/android/twin/build_apk.sh',str(apk),'com.holmes.leanquiet','Lean Quiet',
                    'platforms.headless.TwinDemo','x86_64'],cwd=scratch,stdout=log,stderr=subprocess.STDOUT,timeout=600,check=True)
            (case/'apk.sha256').write_text(hashlib.sha256(apk.read_bytes()).hexdigest()+'\n')
            exercise(args.serial,apk,case,expected)
    exercise(args.serial,ROOT/'out/lifecycle.apk',out/'restored')
    print(f'android lifecycle controls: {len(cases)} refused; restored suite passes',flush=True)


if __name__=='__main__': main()
