#!/usr/bin/env python3
"""Review regressions: weight, lazy startup, metric index and memo contract.
Run alone: restores every source mutation before the next build.
"""
from pathlib import Path
import os
import subprocess

ROOT = Path(__file__).resolve().parents[2]
os.chdir(ROOT)
OUT = ROOT/'out/font-review-negative'
OUT.mkdir(parents=True, exist_ok=True)

def run(cmd):
    p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return p.returncode, p.stdout

def fault(name, path, old, new, cmd, expected, build=False):
    p = ROOT/path
    original = p.read_text()
    assert old in original, name
    try:
        p.write_text(original.replace(old,new,1))
        log = ''
        if build:
            rc,log = run(['lake','build','font_contract'])
            assert rc == 0, (name,log[-3000:])
        rc,result = run(cmd)
        log += result
        (OUT/f'{name}.log').write_text(log)
        assert rc != 0 and expected in result, (name,log[-3000:])
        print('rejected:',name,flush=True)
    finally:
        p.write_text(original)

fault('thin-build','tools/cjk_subset.py',"{'wght': 400}","{'wght': 100}",
      ['python3','tools/cjk_subset.py','--out',str(OUT/'thin')], 'not static Regular')
fault('thin-name','tools/cjk_subset.py','updateFontNames=True','updateFontNames=False',
      ['python3','tools/cjk_subset.py','--out',str(OUT/'thin-name')], 'not static Regular')
fault('thin-reference','tests/app/cjk_reference.py','f=regular(locale)',
      "f=TTFont(SOURCE/f'NotoSans{locale}-wght.ttf')",
      ['python3','tests/app/cjk_reference.py','compare'], 'AssertionError')
fault('eager-startup','engine/renderer/Noto.lean','    out := { out with faces :=',
      '    if (Ttf.read bytes).isNone then throw (IO.userError "bad font")\n    out := { out with faces :=',
      ['.lake/build/bin/font_contract'], 'eager parse/selection regression',True)
fault('compact-metrics','engine/renderer/Noto.lean','(a*cell+metrics.units/2)/metrics.units',
      '(a*cell+metrics.units/2)/metrics.units+1',
      ['.lake/build/bin/font_contract'], 'running Font metrics',True)
fault('memo-hit','engine/renderer/Ttf/Memo.lean','if found.isSome then return found',
      'if found.isSome then return found.map fun b => { b with advance := b.advance+1 }',
      ['.lake/build/bin/font_contract'], 'every field and byte',True)
fault('memo-miss','engine/renderer/Ttf/Memo.lean','return { b with pixels }',
      'return { b with pixels, advance := b.advance+1 }',
      ['.lake/build/bin/font_contract'], 'every field and byte',True)
rc,log = run(['bash','tests/app/font_contract.sh'])
(OUT/'restored.log').write_text(log)
assert rc == 0, log[-3000:]
print('7 controls rejected; restored compact/lazy/memo suite passes',flush=True)
