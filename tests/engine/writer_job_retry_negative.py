#!/usr/bin/env python3
"""Strict completed assertions for real SQLite retry ownership and empty jobs."""
from pathlib import Path
import os, signal, stat, subprocess, sys
root, logs = [Path(x).resolve() for x in sys.argv[1:3]]
logs.mkdir(parents=True, exist_ok=True)
cap=['systemd-run','--user','--scope','-p','MemoryMax=48G','-p','MemorySwapMax=0']

def run(args,name,diagnostics=False):
    if diagnostics:
        assert sys.platform=='linux' and stat.S_ISCHR(os.stat('/dev/full').st_mode), 'Linux /dev/full required'
    failure_sink=open('/dev/full','wb') if diagnostics else None
    try:
        p=subprocess.Popen(args,cwd=root,stdout=subprocess.PIPE,
            stderr=failure_sink if diagnostics else subprocess.STDOUT,text=True,start_new_session=True)
        try: output,_=p.communicate(timeout=240)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL); output,_=p.communicate()
            (logs/(name+'.log')).write_text(output+'\nTIMEOUT (not an accepted control)\n'); raise
    finally:
        if failure_sink: failure_sink.close()
    (logs/(name+'.log')).write_text(output)
    return p.returncode,output

def build(target,name):
    code,out=run(cap+['lake','build',target],name+'-build')
    assert code==0,(name,'must compile',out[-2000:])

def exercise(target,name,failures=()):
    data=logs/(name+'-db')
    args=[str(root/'.lake/build/bin'/target),str(data)]
    code,out=run(args,name,target=='writer_diagnostics')
    expected_db={'empty_jobs':['quiet.db'], 'writer_job_retry':['publication.db'],
        'writer_diagnostics':['checkpoint/publication.db','job/publication.db']}[target]
    assert all((data/p).is_file() for p in expected_db),(name,'missing retained database')
    assert not any(x in out.lower() for x in ['panic','uncaught exception','segmentation fault','assertion violation',
        'unexpected writer diagnostics fixture error']),out
    actual=[x.removeprefix('FAIL: ') for x in out.splitlines() if x.startswith('FAIL: ')]
    assert actual==list(failures),(name,actual,list(failures))
    total={'empty_jobs':10,'writer_job_retry':11,'writer_diagnostics':11}[target]
    suite={'empty_jobs':'empty-jobs','writer_job_retry':'writer-job-retry','writer_diagnostics':'writer-diagnostics'}[target]
    assert code==(1 if failures else 0) and f'{suite}: {total-len(failures)} passed, {len(failures)} failed' in out,(name,code,out)

def once(text,old,new):
    assert text.count(old)==1,old
    return text.replace(old,new)

commands=root/'app/Commands.lean'; screen=root/'app/Screen.lean'
c=commands.read_text(); s=screen.read_text()
writer='def Writer.submit (w : Writer) (j : Job) : IO Unit := do\n  if j.ops.isEmpty then return\n'
app='def submit (j : Job) : M Unit := do\n  if j.ops.isEmpty then return\n'
retry='      w.jobs.modify (·.push j)\n'
cases=[
 ('empty-writer-admission',commands,once(c,writer,writer.replace('  if j.ops.isEmpty then return\n','')),'empty_jobs',[
  'empty maintenance writes do not occupy either real writer FIFO',
  'empty maintenance writes do not inflate real writer busy accounting']),
 ('empty-app-admission',screen,once(s,app,app.replace('  if j.ops.isEmpty then return\n','')),'empty_jobs',[
  'empty writes do not accumulate parked jobs while the app is inactive']),
 ('refuse-all-writer-jobs',commands,once(c,writer,writer.replace('if j.ops.isEmpty','if true')),'empty_jobs',[
  'nonempty signed submission retains its actual writer ownership',
  'nonempty signed submission still commits a valid SQLite op',
  'nonempty selected job balances actual busy accounting']),
 ('refuse-all-app-jobs',screen,once(s,app,app.replace('if j.ops.isEmpty','if true')),'empty_jobs',[
  'nonempty parked write retains its original batch',
  'nonempty parked write retains its recovery journal']),
 ('discard-failed-job',commands,once(c,retry,'      w.busy.modify (· - 1)\n'),'writer_job_retry',[
  'failed job rejoins its own FIFO behind retained work',
  'failed attempt retains exactly one busy owner without counting a commit',
  'repeated failure does not duplicate or discharge its busy owner',
  'failed retries preserve the reserved background slot',
  'only the originally refused job remains queued before recovery',
  'the retained signed job commits after the actual SQL fault is removed',
  'successful recovery discharges every admission exactly once',
  'actual catalog records healthy work before the recovered job without duplicates']),
 ('double-count-retry',commands,once(c,retry,'      w.submit j\n'),'writer_job_retry',[
  'failed attempt retains exactly one busy owner without counting a commit',
  'repeated failure does not duplicate or discharge its busy owner',
  'failed retries preserve the reserved background slot',
  'successful recovery discharges every admission exactly once']),
 ('retry-resets-phase',commands,once(c,retry,'      w.jobs.modify fun q => { q.push j with slot := Engine.Sync.Inbox.Priority.first }\n'),'writer_job_retry',[
  'failed retries preserve the reserved background slot',
  'only the originally refused job remains queued before recovery',
  'the retained signed job commits after the actual SQL fault is removed',
  'successful recovery discharges every admission exactly once',
  'actual catalog records healthy work before the recovered job without duplicates']),
 ('checkpoint-diagnostic-throws',commands,once(c,
  '    discard <| (IO.eprintln s!"writer: checkpoint: {e}").toBaseIO\n',
  '    IO.eprintln s!"writer: checkpoint: {e}"\n'),'writer_diagnostics',[
  'checkpoint diagnostic error cannot escape the selected writer turn',
  'selected signed write commits while checkpoint table and stderr fail',
  "diagnostic failure cannot lose the selected job's busy ownership",
  'later real checkpoint recovery preserves the committed signed write',
  'diagnostic recovery has exactly one actual catalog entry']),
 ('job-diagnostic-throws',commands,once(c,
  '      discard <| (IO.eprintln s!"writer: {e}").toBaseIO\n',
  '      IO.eprintln s!"writer: {e}"\n'),'writer_diagnostics',[
  'job diagnostic error cannot stop the writer after retaining its retry']),
]
for target in ['empty_jobs','writer_job_retry','writer_diagnostics']:
    build(target,target+'-baseline'); exercise(target,target+'-baseline')
try:
    for name,path,mutant,target,failures in cases:
        try:
            path.write_text(mutant); (logs/(name+'.lean')).write_text(mutant)
            build(target,name); exercise(target,name,failures)
            print('rejected:',name,flush=True)
        finally:
            commands.write_text(c); screen.write_text(s)
finally:
    commands.write_text(c); screen.write_text(s)
for target in ['empty_jobs','writer_job_retry','writer_diagnostics']:
    build(target,target+'-restored'); exercise(target,target+'-restored')
print('writer ownership:10 empty-job,11 selective-SQL,11 actual OS diagnostic checks;9 compiling controls;restored pass',flush=True)
