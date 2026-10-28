#!/usr/bin/env python3
"""Run deliberate faults against the real proofs/tests, restoring after each.
Run after tests/noto.sh, with Lake on PATH. Never run beside another build.
"""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'out/noto-negative'
OUT.mkdir(parents=True, exist_ok=True)
os.chdir(ROOT)
SELECT = set(sys.argv[1:])
rejected = []

def command(args):
    p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return p.returncode, p.stdout

def fault(name, file, old, new, proof=False, reference=False, kern=False):
    if SELECT and name not in SELECT:
        return
    path = ROOT / file
    saved = path.read_text()
    assert old in saved, (name, 'mutation missing')
    try:
        path.write_text(saved.replace(old, new, 1))
        rc, log = command(['lake', 'build', 'Quiet.Ttf.Laws' if proof else 'noto'])
        if proof:
            assert rc != 0 and 'error: Quiet/Ttf/Laws.lean:' in log, (name, log[-2000:])
        else:
            assert rc == 0, (name, 'did not compile', log[-2000:])
            rc, run = command(['.lake/build/bin/noto', 'out/noto'])
            log += run
            if rc == 0 and kern:
                rc, run = command(['lake', 'env', 'lean', '--run', 'tests/noto_kern.lean'])
                log += run
            if rc == 0 and reference:
                rc, run = command(['python3', 'tests/noto_reference.py', 'compare', 'out/noto'])
                log += run
            assert rc != 0, (name, 'negative control unexpectedly passed')
        (OUT / (name + '.log')).write_text(log)
        rejected.append(name)
        print('rejected:', name, flush=True)
    finally:
        path.write_text(saved)

fault('byte-value', 'Quiet/Ttf/Bytes.lean', 'some b[i].toNat', 'some (b[i].toNat + 1)', proof=True)
fault('cmap-lookup', 'Quiet/Ttf/Cmap.lean', '.map (·.glyph c)', '.map (fun e => e.glyph c + 1)', proof=True)
fault('cmap12-start', 'Quiet/Ttf/Cmap.lean', 'first + c - e.lo', 'first + c - e.lo + 1', proof=True)
fault('cmap4-delta', 'Quiet/Ttf/Cmap.lean', '((c : Int) + d)', '((c : Int) + d + 1)', proof=True)
fault('cmap4-missing', 'Quiet/Ttf/Cmap.lean', 'if g == 0 then 0 else', 'if g == 0 then 1 else', proof=True)
fault('coverage-value', 'Quiet/Ttf/Raster.lean', 'min 255 (samples', 'min 254 (samples', proof=True)
fault('bitmap-check', 'Quiet/Ttf/Raster.lean', 'if b.Valid then some b else none', 'some b', proof=True)
fault('raster-check', 'Quiet/Ttf/Raster.lean', 'checked (← rasterRaw f glyph size cell)', 'pure (← rasterRaw f glyph size cell)', proof=True)
fault('nonvacuity', 'Quiet/Ttf/Raster.lean', 'if b.Valid then some b else none', 'none', proof=True)
fault('curve-precision', 'Quiet/Ttf/Raster.lean', '(bend * 64)', '(bend * 4)', reference=True)
fault('composite-matrix', 'Quiet/Ttf/Read.lean', 'x := xx * p.x + yx * p.y, y := xyM * p.x + yy * p.y', 'x := xx * p.x + xyM * p.y, y := yx * p.x + yy * p.y', reference=True)
fault('glyph-cache', 'Quiet/Ttf/Memo.lean', '@[implemented_by bitmapImpl]', '-- Memoization removed for the negative control.')
fault('density', 'Quiet/Font.lean', 'max 16 (min 64 ((source * density + 210) / 420))', 'source')
fault('font-truncation', 'Quiet/Ttf/Read.lean', '  let f ← readHeader b', '  if b.size == 0 then return default\n  let f ← readHeader b')
fault('composite-cycle', 'Quiet/Ttf/Read.lean', '    if fuel == 0 || ancestors.contains glyph then failure else do', '    if ancestors.contains glyph then return #[]\n    if fuel == 0 then failure else do')
fault('real-advance', 'Quiet/Ttf/Read.lean', '((f.advances[glyph]?.getD 0) * size + f.units / 2) / f.units', '((f.advances[glyph]?.getD 0) * size + f.units / 2) / f.units + 1', reference=True)
fault('left-clipping', 'Quiet/Ttf/Blit.lean', 'if px < 0 then continue', 'if false then continue')
fault('kern-sign', 'Quiet/Ttf/Read.lean', '(f.kern[(left, right)]?.getD 0) * (size : Int)', '-(f.kern[(left, right)]?.getD 0) * (size : Int)', kern=True)
rc, log = command(['bash', 'tests/noto.sh'])
(OUT / 'restored.log').write_text(log)
assert rc == 0, log[-3000:]
print(f'{len(rejected)} negative controls rejected; restored source passes', flush=True)
