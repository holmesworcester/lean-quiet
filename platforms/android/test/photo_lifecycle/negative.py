#!/usr/bin/env python3
"""Compiled actual Main APK controls for pending-photo lifetime ownership."""
from pathlib import Path
import argparse,difflib,hashlib,json,os,shutil,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'platforms/android/test/lifecycle'))
from crashes import crash_lines

J='platforms/android/twin/java/com/holmes/leanquiet/LeanActivity.java'
C='platforms/android/twin/activity.c'
CASES=[
 ('omit-cancellation',J,'if (cancelledPhoto != 0) nPhoto(cancelledPhoto, 2, 0, 0, null);',
  '/* broken: no terminal result for destroyed owner */',
  'recreated picker clears App pending request'),
 ('wrong-cancellation-token',J,'nPhoto(cancelledPhoto, 2, 0, 0, null);',
  'nPhoto(cancelledPhoto + 1, 2, 0, 0, null);',
  'recreated picker clears App pending request'),
 ('cancel-ordinary-pause',J,'  @Override protected void onPause() {',
  '  @Override protected void onPause() {\n    if (photoToken != 0) nPhoto(photoToken, 2, 0, 0, null);',
  'ordinary picker pause still yields one decoded photo'),
 ('accept-retired-photo-owner',C,'if (ba_current(env, activity)) lq_photo_publish',
  'if (true) lq_photo_publish',
  'retired Activity cannot complete replacement photo request'),
]

def exercise(serial,apk,out,expected=None):
    out.mkdir(parents=True,exist_ok=True)
    proc=subprocess.run([sys.executable,str(ROOT/'platforms/android/test/photo_lifecycle/exercise.py'),
        '--serial',serial,'--apk',str(apk),'--out',str(out)],cwd=ROOT,capture_output=True,text=True,timeout=240)
    output=proc.stdout+proc.stderr;(out/'driver.log').write_text(output);print(output,end='',flush=True)
    assert proc.returncode>=0 and 'Traceback' not in output,'host exception/signal is not a control result'
    result=json.loads((out/'result.json').read_text())
    owner=json.loads((out/'owner.json').read_text())
    target,external=crash_lines((out/'logcat.txt').read_text(),owner['pid'])
    (out/'external-crashes.txt').write_text('\n'.join(external)+'\n')
    assert not target,'target crash is not a valid control'
    if expected is None:
        assert proc.returncode==0 and not result['failures'],'positive actual photo lifetime fixture failed'
    else:
        assert proc.returncode==1 and result['failures']==[expected],(expected,result['failures'])
        print('refused: '+out.name+' (compiled; exact actual App assertion)',flush=True)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--serial',required=True)
    parser.add_argument('--out',type=Path,default=ROOT/'out/photo-lifecycle')
    args=parser.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    exercise(args.serial,ROOT/'out/photo-main.apk',out/'baseline')
    with tempfile.TemporaryDirectory(prefix='photo-lifecycle-negative-',dir=os.environ['TMPDIR']) as temp:
        scratch=Path(temp)
        shutil.copytree(ROOT,scratch,dirs_exist_ok=True,ignore=shutil.ignore_patterns('.git','.lake','out','target','__pycache__'))
        subprocess.run(['cp','-a','--reflink=auto',str(ROOT/'.lake'),str(scratch)],check=True)
        (scratch/'out').mkdir()
        for name in ['leanrt','cache','stdc']:
            subprocess.run(['cp','-a','--reflink=auto',str(ROOT/'out'/name),str(scratch/'out')],check=True)
        originals={file:(scratch/file).read_text() for file in [J,C]}
        for name,file,old,new,expected in CASES:
            for path,source in originals.items():(scratch/path).write_text(source)
            source=originals[file];assert source.count(old)==1,(name,'missing/ambiguous anchor')
            (scratch/file).write_text(source.replace(old,new))
            case=out/name;case.mkdir(exist_ok=True)
            (case/'source.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),source.replace(old,new).splitlines(True),fromfile=file,tofile=file)))
            apk=case/'mutant.apk'
            with (case/'build.log').open('w') as log:
                subprocess.run(['systemd-run','--user','--scope','-p','MemoryMax=48G','-p','MemorySwapMax=0',
                    'bash','platforms/android/twin/build_apk.sh',str(apk),'com.holmes.leanquiet','Lean Quiet','Main','x86_64'],
                    cwd=scratch,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
            (case/'apk.sha256').write_text(hashlib.sha256(apk.read_bytes()).hexdigest()+'\n')
            exercise(args.serial,apk,case,expected)
    exercise(args.serial,ROOT/'out/photo-main.apk',out/'restored')
    print('android photo lifetime:4 compiling controls refused; restored suite passes',flush=True)

if __name__=='__main__':main()
