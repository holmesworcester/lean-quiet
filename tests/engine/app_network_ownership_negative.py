#!/usr/bin/env python3
"""Only compiled, completed, exact real-resource assertion failures pass."""
from pathlib import Path
import os
import re
import signal
import subprocess
import sys

root, logs=(Path(value).resolve() for value in sys.argv[1:3])
logs.mkdir(parents=True,exist_ok=True)
cap=['systemd-run','--user','--scope','-p','MemoryMax=48G','-p','MemorySwapMax=0']


def run(args,name,timeout):
    child=subprocess.Popen(args,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                           text=True,start_new_session=True)
    try:
        text,_=child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid,signal.SIGKILL);text,_=child.communicate()
        (logs/(name+'.log')).write_text(text+'\nTIMEOUT (not an accepted control)\n')
        raise
    (logs/(name+'.log')).write_text(text)
    return child.returncode,text


def build(name):
    code,text=run(cap+['lake','build','app_network_ownership'],name+'-build',360)
    assert code==0,(name,'must compile',text[-3000:])


def exercise(name,mode='all',expected=()):
    data=logs/(name+'-db')
    code,text=run([str(root/'.lake/build/bin/app_network_ownership'),str(data),mode],name,40)
    modes=['log','frame','adopt-log','adopt-frame','stop'] if mode=='all' else [mode]
    assert all((data/item/'app.db').is_file() for item in modes),(name,'missing actual SQLite fixture')
    assert not any(marker in text.lower() for marker in ['panic','unexpected app ownership fixture error',
        'uncaught exception','segmentation fault','assertion violation']), (name,text)
    failures=[line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    summary=re.search(r'app-network-ownership: (\d+) passed, (\d+) failed',text)
    assert summary and int(summary[2])==len(failures),(name,text)
    assert text.count('observed App failure: expected ownership ')==len([m for m in modes if m!='stop']),(name,text)
    if expected:
        assert code==1 and sorted(failures)==sorted(expected),(name,code,failures,text)
    else:
        assert code==0 and not failures and summary[1]=='52',(name,text)


def once(s,a,b):
    assert s.count(a)==1,('production anchor must be unique',a)
    return s.replace(a,b)


source=root/'app/Screen.lean';original=source.read_text()
retained='shared ownership retains the original boot or live Runner after rollback'
stops='shared owner retains both actual stop/replay tasks despite frame rollback'
controls=[
 ('forget-boot-slot','frame',lambda s:once(s,
    '    set { n with boot := some task }\n','    pure ()\n'),[retained]),
 ('forget-adopted-runner','adopt-frame',lambda s:once(s,
    '| .ok runner => set { n with boot := none, runner := some runner }',
    '| .ok _ => set { n with boot := none, runner := none }'),[retained]),
 ('forget-stop-slot','stop',lambda s:once(s,
    '    stopping := if failed then n.stopping else some stopping\n',
    '    stopping := n.stopping\n'),[stops]),
 ('forget-replay-slot','stop',lambda s:once(s,
    '    replay := some replay\n','    replay := none\n'),[stops]),
 ('replace-stopping-generation','stop',lambda s:once(s,
    '  if n.runner.isNone && n.boot.isNone then return false\n',''),
  ['repeated suspend keeps exactly the original stop task',
   'repeated suspend keeps exactly the original replay task']),
]
build('baseline');exercise('baseline')
try:
    for name,mode,mutate,expected in controls:
        source.write_text(mutate(original));build(name);exercise(name,mode,expected)
        print('rejected: '+name+' (compiled, exact actual ownership assertion)',flush=True)
finally:
    source.write_text(original)
build('restored');exercise('restored')
print('app network ownership:52 actual checks, five compiling controls; restored pass',flush=True)
