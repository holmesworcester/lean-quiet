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

# Regression for the original vacuity failures: a universal Good hypothesis
# must no longer promise a roundtrip before supported-input premises are supplied.
for label, source in [
    ('seal roundtrip without size premises', '''import ops.community.Keys
example (g : Community.cryptoSeal.Good) (k n ad p : ByteArray) :
    Community.cryptoSeal.dec k n ad (Community.cryptoSeal.enc k n ad p) = some p := by
  simpa using g.dec_enc k n ad p
'''),
    ('Noise roundtrip without key premise', '''import ops.connection.Noise
open Connection.Noise
example (g : suite.Good) (k ad p : ByteArray) :
    suite.dec k 0 ad (suite.enc k 0 ad p) = some p := by
  simpa using g.dec_enc k (0 : Nat) ad p
'''),
    ('seal roundtrip without payload bound', '''import ops.community.Keys
open Community
example (g : cryptoSeal.Good) (k n ad p : ByteArray)
    (hk : k.size = 32) (hn : n.size = 24) (ha : ad.size < Seal.maxAssociatedDataSize) :
    cryptoSeal.dec k n ad (cryptoSeal.enc k n ad p) = some p := by
  simpa using g.dec_enc k n ad p hk hn ha
'''),
    ('seal roundtrip without associated-data bound', '''import ops.community.Keys
open Community
example (g : cryptoSeal.Good) (k n ad p : ByteArray)
    (hk : k.size = 32) (hn : n.size = 24) (hp : p.size < Seal.maxPlaintextSize) :
    cryptoSeal.dec k n ad (cryptoSeal.enc k n ad p) = some p := by
  simpa using g.dec_enc k n ad p hk hn hp
'''),
    ('Noise roundtrip without payload bound', '''import ops.connection.Noise
open Connection.Noise
example (g : suite.Good) (k ad p : ByteArray) (hk : suite.ValidKey k) (ha : suite.ValidAD ad) :
    suite.dec k 0 ad (suite.enc k 0 ad p) = some p := by
  simpa using g.dec_enc k hk 0 ad p ha
'''),
    ('Noise roundtrip without associated-data bound', '''import ops.connection.Noise
open Connection.Noise
example (g : suite.Good) (k ad p : ByteArray) (hk : suite.ValidKey k) (hp : suite.ValidPayload p) :
    suite.dec k 0 ad (suite.enc k 0 ad p) = some p := by
  simpa using g.dec_enc k hk 0 ad p hp
'''),
]:
    with tempfile.TemporaryDirectory(prefix='quiet-vacuity-contract-',
                                    dir=os.environ.get('TMPDIR', '/mnt/storage/holmes-tmp')) as tmp:
        fixture = Path(tmp) / 'Broken.lean'
        fixture.write_text(source)
        result = subprocess.run(['lake', 'env', 'lean', str(fixture)], cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode == 0 or 'type mismatch' not in result.stdout.lower():
            raise SystemExit(f'contract control did not fail as expected: {label}\n{result.stdout}{result.stderr}')
    print(f'rejected control: {label}')
