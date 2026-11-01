#!/usr/bin/env python3
"""Compile one source-level mutation of the actual app.Screen module, without editing it."""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess
import tempfile

p=argparse.ArgumentParser()
p.add_argument('control',choices=['old-geometry-lease','ignore-content','unowned-long-send','hidden-composer','latest-continue'])
p.add_argument('--out',type=Path,required=True)
args=p.parse_args()
os.environ.setdefault('ELAN_HOME','/mnt/storage/elan')
os.environ.setdefault('TMPDIR','/mnt/storage/holmes-tmp')
root=Path(__file__).resolve().parents[4]
s=(root/'app/Screen.lean').read_text()
def once(old,new):
    global s
    if s.count(old)!=1:raise RuntimeError('App control anchor changed: '+old)
    s=s.replace(old,new)
if args.control=='old-geometry-lease':
    once('| .action _ _ _ [.send] => if !(← onEvent e) then return none',
         '| .action _ _ _ [.send] => if let some false ← owned lease (onEvent e) then return none')
elif args.control=='ignore-content':
    once('refusal == 0 && s.editor.contentKey == editorContentKey s &&','refusal == 0 &&')
elif args.control=='latest-continue':
    once('let field := (submission.map (·.text)).getD s.field','let field := s.field')
elif args.control=='hidden-composer':
    once('''    if (← get).page != .chat then
      if let some action := submission then discard <| (← get).io.editorIo.action action.ticket 2
      say "Open a conversation to send a message."
      return true
''','')
else:
    once('if !(long && hit == .continue_) then onPageAct hit submission refusal',
         'onPageAct hit submission refusal')
    # Both the long-gesture and unowned-user guards intentionally protect this
    # path. Restoring its old behavior requires removing both protections.
    once('| .send => if !long then sendNow submission refusal',
         '| .send => sendNow submission refusal')
    once('let refusal := if refusal.isNone && submission.isNone && (← get).editor.enabled == some true then some 2 else refusal',
         'let refusal := refusal')
args.out.mkdir(parents=True,exist_ok=True)
(args.out/'Screen.lean').write_text(s)
lake=str(Path(os.environ['ELAN_HOME'])/'bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=root,text=True).strip()
path=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=root,text=True).strip()
path=':'.join(str((root/x).resolve()) if not Path(x).is_absolute() else x for x in path.split(':') if x)
with tempfile.TemporaryDirectory(prefix='owned-app-control-',dir=os.environ['TMPDIR']) as tmp:
    tmp=Path(tmp)
    shutil.copytree(root/'.lake/build/lib/lean',tmp,copy_function=os.symlink,dirs_exist_ok=True)
    for artifact in (tmp/'app').glob('Screen.*'):
        if artifact.is_symlink():artifact.unlink()
    (tmp/'app/Screen.lean').write_text(s)
    # Keep the real baseline module's code-generation namespace. Lake adds
    # a package prefix; a private direct-Lean diagnostic may have no prefix.
    baseline=(root/'.lake/build/ir/app/Screen.c').read_text()
    setup=[]
    if re.search(r'LEAN_EXPORT [^;\n]*\blp_quiet_App_',baseline):
        setup=['--setup',str(root/'.lake/build/ir/app/Screen.setup.json')]
    subprocess.run([lean,*setup,'-o','app/Screen.olean','-c',str((args.out/'Screen.c').resolve()),'app/Screen.lean'],
        cwd=tmp,env=dict(os.environ,LEAN_PATH=str(tmp)+':'+path),check=True,timeout=120)
