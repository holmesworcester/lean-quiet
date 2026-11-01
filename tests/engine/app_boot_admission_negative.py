#!/usr/bin/env python3
"""Compile real App boot defects; only designated completed assertion failures pass."""
from pathlib import Path
import os
import re
import signal
import subprocess
import sys

root, logs = (Path(value).resolve() for value in sys.argv[1:3])
logs.mkdir(parents=True, exist_ok=True)
cap = ['systemd-run', '--user', '--scope', '-p', 'MemoryMax=48G', '-p', 'MemorySwapMax=0']


def run(command, name, timeout):
    child = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        text, _ = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        text, _ = child.communicate()
        (logs/(name+'.log')).write_text(text+'\nTIMEOUT (not an accepted control)\n')
        raise
    (logs/(name+'.log')).write_text(text)
    return child.returncode, text


def build(name):
    code, text = run(cap+['lake','build','app_boot_admission'],name+'-build',360)
    assert code == 0, (name,'must compile',text[-3000:])


def exercise(name, required=(), permitted=()):
    data=logs/(name+'-db')
    code,text=run([str(root/'.lake/build/bin/app_boot_admission'),str(data)],name,30)
    assert (data/'app.db').is_file(),(name,'missing actual SQLite fixture')
    assert not any(marker in text.lower() for marker in ['panic','unexpected app boot fixture error',
        'uncaught exception','segmentation fault','assertion violation']), (name,text)
    failures=[line.removeprefix('FAIL: ') for line in text.splitlines() if line.startswith('FAIL: ')]
    summary=re.search(r'app-boot-admission: (\d+) passed, (\d+) failed',text)
    assert summary and int(summary[2])==len(failures),(name,text)
    if required:
        assert code == 1 and set(required)<=set(failures),(name,code,text)
        assert set(failures)<=set(permitted or required),(name,'unexpected assertion',text)
    else:
        assert code == 0 and not failures and summary[1]=='13',(name,text)


def once(s,old,new):
    assert s.count(old)==1,('unique production anchor changed',old)
    return s.replace(old,new)


source=root/'app/Screen.lean';original=source.read_text()
installed='first network service installs an owned boot task before earlier work finishes'
parked='continuing App submissions park in accepted order behind boot'
backlog='later App writes cannot extend the pre-boot Writer backlog'
waited='retained boot does not install a runner ahead of earlier Writer commits'
no_overtake='no later signed operation overtakes the paused pre-boot write'
journal='checkpoint owns every parked and pre-boot accepted byte'
order='real SQLite catalog orders the pre-boot write before all later submissions'
controls=[
 ('wait-before-owning-boot',lambda s:once(s,
    '  let listen := ((← listenHints).head?).getD s!"127.0.0.1:{port}".toUTF8\n',
    '  if (← s.wr.busy.get) > 0 then return\n  let listen := ((← listenHints).head?).getD s!"127.0.0.1:{port}".toUTF8\n'),
  [installed,parked,backlog,waited],[]),
 ('open-before-earlier-writes',lambda s:once(s,
    '    while (← writer.busy.get) > 0 do IO.sleep 2\n',''),
  [waited,no_overtake], [waited,no_overtake,parked,journal,order]),
]
build('baseline');exercise('baseline')
try:
    for name,mutate,required,permitted in controls:
        source.write_text(mutate(original));build(name);exercise(name,required,permitted)
        print('rejected: '+name+' (compiled, actual App/Writer/SQLite assertion)',flush=True)
finally:
    source.write_text(original)
build('restored');exercise('restored')
print('app boot admission:13 actual checks, two compiling controls; restored pass',flush=True)
