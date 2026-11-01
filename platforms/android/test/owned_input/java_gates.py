#!/usr/bin/env python3
"""Repackage an already-built actual app with test-only callback barriers.

Only the scheduling of the original Java Runnable changes. Its entire body,
the real native library, App code, resources, manifest and signing key remain.
No test barrier is installed in shipping sources.
"""
from pathlib import Path
import argparse
import os
import shutil
import subprocess
import tempfile
import zipfile

p=argparse.ArgumentParser()
p.add_argument('--base',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--sources',type=Path,required=True)
p.add_argument('--control',choices=['blind-clear','ownerless-editable','forget-focus','overwrite-handoff'])
args=p.parse_args()
root=Path(__file__).resolve().parents[4]
sdk=Path(os.environ.get('ANDROID_SDK',Path.home()/'android-sdk'))
bt=max((sdk/'build-tools').iterdir(),key=lambda x:tuple(map(int,x.name.split('.'))))
jar=max((sdk/'platforms').glob('android-*'),key=lambda x:int(x.name[8:]))/'android.jar'
args.sources.mkdir(parents=True,exist_ok=True)
shutil.copytree(root/'platforms/android/twin/java',args.sources,dirs_exist_ok=True)
source=args.sources/'com/holmes/leanquiet/LeanActivity.java'
s=source.read_text()
def replace_once(old,new):
    global s
    if s.count(old)!=1:raise RuntimeError('changed test barrier anchor: '+old)
    s=s.replace(old,new)
helpers='''
  // Test-only: retain one original callback without blocking the Android UI.
  public static volatile boolean ownedTestHoldClear, ownedTestHoldInstall, ownedTestFailClear;
  public static volatile Runnable ownedTestClear, ownedTestInstall;
  private static final Object ownedTestLock=new Object();
  private void ownedTestQueueClear(Runnable callback) {
    synchronized(ownedTestLock) {
      if(ownedTestHoldClear) {
        if(ownedTestClear!=null)throw new AssertionError("duplicate retained clear callback");
        ownedTestClear=callback;return;
      }
    }
    runOnUiThread(callback);
  }
  private void ownedTestQueueInstall(Runnable callback) {
    synchronized(ownedTestLock) {
      if(ownedTestHoldInstall) {
        if(ownedTestInstall!=null)throw new AssertionError("duplicate retained install callback");
        ownedTestInstall=callback;return;
      }
    }
    runOnUiThread(callback);
  }
  public void ownedTestReleaseClear() {
    Runnable callback;
    synchronized(ownedTestLock){ownedTestHoldClear=false;callback=ownedTestClear;ownedTestClear=null;}
    if(callback!=null)runOnUiThread(callback);
  }
  public void ownedTestReleaseInstall() {
    Runnable callback;
    synchronized(ownedTestLock){ownedTestHoldInstall=false;callback=ownedTestInstall;ownedTestInstall=null;}
    if(callback!=null)runOnUiThread(callback);
  }
'''
replace_once('  private long editorOwner, editorRevision;',helpers+'\n  private long editorOwner, editorRevision;')
replace_once('''    runOnUiThread(() -> {
      long next,revision;byte[] bytes;int kind;''','''    ownedTestQueueInstall(() -> {
      long next,revision;byte[] bytes;int kind;''')
replace_once('  public void clearAction(long ticket,long owner,long revision) {',
             '  public void clearAction(long ticket,long owner,long revision) {\n    if(ownedTestFailClear){ownedTestFailClear=false;throw new IllegalStateException("owned test clear-post failure");}')
replace_once('''    runOnUiThread(() -> {
      long token,expectedOwner,expectedRevision;''','''    ownedTestQueueClear(() -> {
      long token,expectedOwner,expectedRevision;''')
if args.control=='blind-clear':
    replace_once('if(editorOwner==expectedOwner&&editorRevision==expectedRevision&&expectedRevision!=0)',
                 'if(editorOwner==expectedOwner)')
elif args.control=='ownerless-editable':
    replace_once('    edit.setEnabled(false);','    edit.setEnabled(true);')
elif args.control=='forget-focus':
    replace_once('      if(changed)imm.restartInput(edit);\n      if(imeWanted)applyIme();',
                 '      if(changed)imm.restartInput(edit);')
elif args.control=='overwrite-handoff':
    replace_once('boolean preserve=kind==5&&editorOwner!=0;',
                 'boolean preserve=false;')
source.write_text(s)
with tempfile.TemporaryDirectory(prefix='owned-input-java-',dir=os.environ['TMPDIR']) as tmp:
    tmp=Path(tmp);(tmp/'classes').mkdir();(tmp/'dex').mkdir()
    def run(args):subprocess.run([str(a) for a in args],check=True,timeout=120)
    run(['javac','--release','17','-nowarn','-classpath',jar,'-d',tmp/'classes',*args.sources.rglob('*.java')])
    run([bt/'d8','--min-api','30','--lib',jar,'--output',tmp/'dex',*(tmp/'classes').rglob('*.class')])
    with zipfile.ZipFile(args.base) as before,zipfile.ZipFile(tmp/'app.apk','w') as after:
        for info in before.infolist():
            if info.filename!='classes.dex' and not info.filename.startswith('META-INF/'):
                after.writestr(info,before.read(info.filename))
        after.write(tmp/'dex/classes.dex','classes.dex',zipfile.ZIP_DEFLATED)
    run([bt/'zipalign','-f','4',tmp/'app.apk',tmp/'aligned.apk'])
    run([bt/'apksigner','sign','--ks',root/'platforms/android/twin/debug.keystore',
         '--ks-pass','pass:android','--ks-key-alias','lean','--out',args.out,tmp/'aligned.apk'])
