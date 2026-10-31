"""Reject incorrect concrete outputs and impossible fixture premises in Lean."""
import os
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
for statement in [
    'Pic.fit 4032 3024 2048 = (2048, 1535)',
    'max 4032 3024 ≤ 2048',
    '1 ≤ (0 : Nat)',
    '2048 < max 640 480',
]:
    with tempfile.TemporaryDirectory(prefix='quiet-vacuity-', dir=os.environ.get('TMPDIR', '/mnt/storage/holmes-tmp')) as tmp:
        fixture = Path(tmp) / 'Broken.lean'
        fixture.write_text('import engine.renderer.pic.Laws\nexample : ' + statement + ' := by decide\n')
        result = subprocess.run(['lake', 'env', 'lean', str(fixture)], cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode == 0 or 'error:' not in result.stdout or 'decide' not in result.stdout:
            raise SystemExit(f'control did not fail as expected: {statement}\n{result.stdout}{result.stderr}')
    print(f'rejected control: {statement}')
