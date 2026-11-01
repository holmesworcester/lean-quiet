#!/usr/bin/env python3
"""Actual APK controls: compile successfully, then fail the intended live oracle.
No mutated source is installed in the production source tree.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys

p=argparse.ArgumentParser()
p.add_argument('--serial',required=True);p.add_argument('--avd',required=True)
p.add_argument('--base',type=Path,required=True);p.add_argument('--probe',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--reuse-ir',action='store_true',help='private diagnostic: previously compiled exact local IR')
p.add_argument('--select',nargs='*');p.add_argument('--skip-baseline',action='store_true')
a=p.parse_args();root=Path(__file__).resolve().parents[4];here=Path(__file__).resolve().parent
out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
# The failure must be an assertion in the original real App/JNI exercise,
# with its process still alive. A compiler failure, crash or timeout fails this gate.
cases=[
 ('latest-snapshot','native','repaired real Send commits captured A within five-second diagnostic bound',None),
 ('blind-clear','java','newer B remains the actual App draft',None),
 ('overwrite-handoff','java','same-editor handoff preserves actual Field C',None),
 ('forget-consumed','native','holdclear App draft survives suspension/recreation correctly',None),
 ('empty-latest','native','same-editor handoff cannot overwrite newer App C',None),
 ('empty-read','native','actual App explicitly refuses unreadable captured action','actual App did not explicitly refuse new action'),
 ('old-geometry-lease','app','owned Send survives geometry-only lease change in its actual delivery turn',None),
 ('ignore-content','app','actual App explicitly refuses stale content despite latest-read failure','actual App did not explicitly refuse new action'),
 ('ownerless-editable','java','actual new Field rejects typing before ownership installation','ownerless Field accepted editing'),
 ('forget-focus','java','first tap gains enabled InputConnection and focus after install','installed editor did not honor first pending focus request'),
 ('unowned-long-send','app','held Send button never commits an unowned latest draft',None),
 ('hidden-composer','app','Home explicitly refuses hidden-composer submission','actual App did not explicitly refuse new action'),
 ('consumed-readmit','native','actual JNI cleanup refuses a second send of consumed raw A','already consumed revision was admitted again after clear-post failure'),
 ('latest-continue','app','actual created community has captured A name',None),
]
if a.select:
    if not set(a.select)<={x[0] for x in cases}:raise ValueError('unknown selected control')
    cases=[x for x in cases if x[0] in a.select]
manifest={'source_root':str(root),'base_apk_sha256':hashlib.sha256(a.base.read_bytes()).hexdigest(),
          'reuse_precompiled_ir':a.reuse_ir,'checks':[]}
def run(name,args,expect=0,timeout=240):
    with (out/(name+'.log')).open('w') as log:
        result=subprocess.run([str(x) for x in args],cwd=root,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    if result.returncode!=expect:raise RuntimeError(f'{name}: exit {result.returncode}, expected {expect}; see {out/name}.log')
    return result

def exercise(name,apk,failure=None,cause=None):
    dest=out/name
    run(name,[sys.executable,here/'exercise.py','--serial',a.serial,'--avd',a.avd,'--apk',apk,'--probe',a.probe,'--out',dest],1 if failure else 0)
    result=json.loads((dest/'result.json').read_text())
    if result['failures']!=([failure] if failure else []):raise RuntimeError(f'{name}: unintended oracle: {result["failures"]}')
    if not result['process_alive_before_cleanup']:raise RuntimeError(f'{name}: target process died')
    log=(dest/'logcat.txt').read_text()
    if cause and cause not in log:raise RuntimeError(f'{name}: intended Java assertion missing')
    if 'FATAL EXCEPTION' in log or 'Fatal signal' in log:raise RuntimeError(f'{name}: native/Java crash is not a valid control')
    entry={'name':name,'apk_sha256':hashlib.sha256(apk.read_bytes()).hexdigest(),
           'expected_failure':failure,'passed_assertions':len(result['passed']),'alive':True}
    manifest['checks'].append(entry);(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(name+': '+('expected assertion rejected' if failure else 'passed'),flush=True)

baseline=out/'baseline.apk'
run('baseline-java-build',[sys.executable,here/'java_gates.py','--base',a.base,'--out',baseline,'--sources',out/'baseline-java'])
if not a.skip_baseline:exercise('baseline',baseline)
errors=[]
for name,kind,failure,cause in cases:
    try:
        dest=out/name;dest.mkdir(exist_ok=True)
        if kind=='java':base=a.base;java_control=['--control',name]
        else:
            args=[sys.executable,here/'prepare.py','--out',dest/'native']
            if a.reuse_ir:args+=['--reuse-ir']
            if kind=='native':args+=['--control',name]
            else:
                run(name+'-lean-compile',[sys.executable,here/'app_control.py',name,'--out',dest/'lean'],timeout=180)
                args+=['--app-c',dest/'lean/Screen.c']
            run(name+'-prepare',args)
            base=dest/'native/base.apk'
            run(name+'-native-compile',['bash',dest/'native/build_app.sh',base,'com.holmes.leanquiet','Lean Quiet','Main','x86_64'],timeout=900)
            java_control=[]
        apk=dest/'mutant.apk'
        run(name+'-java-compile',[sys.executable,here/'java_gates.py','--base',base,'--out',apk,'--sources',dest/'java',*java_control])
        exercise(name,apk,failure,cause)
    except Exception as error:
        errors.append({'name':name,'error':repr(error)})
        manifest['gate_errors']=errors
        (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
        print(name+': GATE FAILURE '+repr(error),flush=True)
exercise('restored',baseline)
if errors:raise RuntimeError(f'{len(errors)} control gate failure(s): {errors}')
print(f'owned-input Android: {len(cases)} compiling controls and restored baseline passed',flush=True)
