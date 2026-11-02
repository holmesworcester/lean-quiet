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

# Sized crypto (forensics finding 1). Raw bytes cannot stand for a key or a
# nonce, and the Noise suite's AEAD premise still needs a valid key.
def lean(source, prefix):
    with tempfile.TemporaryDirectory(prefix=prefix, dir=os.environ.get('TMPDIR', '/mnt/storage/holmes-tmp')) as tmp:
        fixture = Path(tmp) / 'Control.lean'
        fixture.write_text(source)
        r = subprocess.run(['lake', 'env', 'lean', str(fixture)], cwd=ROOT, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

for label, source in [
    ('a raw byte array is not a seal key', """import app.community.Op
example (g : Community.cryptoSeal.Good) (k n ad p : ByteArray) :
    Community.cryptoSeal.dec k n ad (Community.cryptoSeal.enc k n ad p) = some p := by
  simpa using g.dec_enc k n ad p
"""),
    ('a raw byte array is not a frame key', """import app.connection.Proofs
example (t : Trust.NativeCrypto) (cid sk n p : ByteArray) :
    Connection.Frame.open Connection.sodium sk (Connection.Frame.seal Connection.sodium cid sk n p) = some (cid, p) :=
  Connection.open_seal_sodium t cid sk n (p := p) (by decide)
"""),
    ('Noise roundtrip without key premise', """import engine.wire.Noise
open Connection.Noise
example (g : suite.Good) (k ad p : ByteArray) :
    suite.dec k 0 ad (suite.enc k 0 ad p) = some p := by
  simpa using g.dec_enc k (0 : Nat) ad p
"""),
    ('Noise roundtrip without payload bound', """import engine.wire.Noise
open Connection.Noise
example (g : suite.Good) (k ad p : ByteArray) (hk : suite.ValidKey k) (ha : suite.ValidAD ad) :
    suite.dec k 0 ad (suite.enc k 0 ad p) = some p := by
  simpa using g.dec_enc k hk 0 ad p ha
"""),
    ('seal roundtrip without payload bound', """import app.community.Op
open Engine Community
example (g : cryptoSeal.Good) (k : Key32) (n : Nonce24) (ad p : ByteArray) (ha : ad.size < Crypto.maxAD) :
    cryptoSeal.dec k n ad (cryptoSeal.enc k n ad p) = some p := by
  simpa using g.dec_enc k n ad p ha
"""),
]:
    code, out = lean(source, 'quiet-vacuity-contract-')
    if code == 0 or 'mismatch' not in out.lower():
        raise SystemExit(f'contract control did not fail as expected: {label}\n{out}')
    print(f'rejected control: {label}')

# Mutation controls: each sized-crypto law, over a broken copy of the code it
# is about, must fail to prove. The unmutated copy must compile first, and
# the mutant's first error must fall inside the named theorem, so neither a
# typo nor an unrelated break can pass as a control.
def theorem_text(path, name):
    lines = (ROOT / path).read_text().split('\n')
    thm = next(i for i, l in enumerate(lines) if l.startswith(f'theorem {name} ') or l == f'theorem {name}')
    start = thm
    if start > 0 and lines[start - 1].endswith('-/'):
        while not lines[start - 1].startswith('/--'):
            start -= 1
        start -= 1
    end = thm + 1
    while end < len(lines) and not (lines[end].startswith('/--') or lines[end].startswith('theorem ') or
                                    lines[end].startswith('def ') or lines[end].startswith('end') or
                                    lines[end].startswith('section') or lines[end].startswith('open ')):
        end += 1
    return '\n'.join(lines[start:end])

def span(text, name):
    lines = text.split('\n')
    start = next(i for i, l in enumerate(lines) if l.startswith(f'theorem {name} ') or l == f'theorem {name}')
    end = start + 1
    while end < len(lines) and not (lines[end].startswith('theorem ') or lines[end].startswith('def ') or
                                    lines[end].startswith('end') or lines[end].startswith('/--')):
        end += 1
    return start + 1, end

def mutant(label, path, old, new, target, extra=''):
    base = (ROOT / path).read_text()
    assert base.count(old) == 1, (label, 'anchor must occur once')
    good = base.replace('\nend Community\n', '\n' + extra + '\nend Community\n', 1) if extra else base
    code, out = lean(good, 'quiet-mutation-base-')
    if code != 0:
        raise SystemExit(f'mutation control base does not compile: {label}\n{out}')
    bad = good.replace(old, new, 1)
    code, out = lean(bad, 'quiet-mutation-')
    errs = [int(m.group(1)) for m in re.finditer(r'Control\.lean:(\d+):\d+: error', out)]
    lo, hi = span(bad, target)
    if code == 0 or not errs or not (lo <= errs[0] <= hi):
        raise SystemExit(f'mutation control did not fail at {target}: {label}\n{out[:3000]}')
    print(f'rejected mutation: {label} (fails {target})')

import re
OP = 'app/community/Op.lean'
NOISE = 'engine/wire/Noise.lean'
SEALED = theorem_text('app/community/Proofs.lean', 'openSealed_seal')
MEMBER = theorem_text('app/community/Proofs.lean', 'member_opens')
mutant('cryptoSeal opens under the zero nonce', OP,
       '  dec k n := Crypto.xchachaOpen k.1 n.1\n', '  dec k _ := Crypto.xchachaOpen k.1 (Bytes.zeros 24).1\n',
       'cryptoSeal_good')
mutant('unbox reads the ephemeral key one byte late', OP,
       '  let epk := b.extract 0 32\n', '  let epk := b.extract 1 33\n', 'unbox_box')
mutant('box leaves out the ephemeral key', OP,
       '  | some bk => epk ++ S.enc bk zeros24 kid k.1\n', '  | some bk => S.enc bk zeros24 kid k.1\n', 'unbox_box')
mutant('openSealed takes its nonce from the end', OP,
       'else openBody S k (Bytes.front sealed (by omega)) c kid (sealed.extract 24 sealed.size)',
       'else openBody S k (Bytes.front (sealed.extract (sealed.size - 24) sealed.size) (by simp; omega)) c kid (sealed.extract 24 sealed.size)',
       'openSealed_seal', extra=SEALED)
mutant('the key id carries the key itself', OP,
       'def kidOf (k : Key32) : B := S.hash ("quiet/content-key/v1".toUTF8 ++ k.1)\n',
       'def kidOf (k : Key32) : B := S.hash ("quiet/content-key/v1".toUTF8 ++ k.1) ++ k.1\n',
       'member_opens', extra=SEALED + '\n' + MEMBER)
mutant('Noise DH without the zero-point check', NOISE,
       '    | some k => if b = (Bytes.zeros 32).1 then none else\n      let r := x25519 k.1 b; if r.size = 32 then some r else none\n',
       '    | some k => let r := x25519 k.1 b; if r.size = 32 then some r else none\n',
       'suite_dh_comm')
mutant('Noise public key of a malformed secret is empty', NOISE,
       '  pub a := match Bytes.of? (n := 32) a with\n    | some k => x25519Base k.1\n    | none => (Bytes.zeros 32).1\n',
       '  pub a := match Bytes.of? (n := 32) a with\n    | some k => x25519Base k.1\n    | none => .empty\n',
       'suite_pub_size')

# The app-level instances, over the code they replaced or a plausible slip:
# the mutant is a copy of the running function, and the instance's own
# proof script, restated over it, must fail.
for label, source, target in [
    ('the old unsized sealFor', """import app.connection.Proofs
namespace Connection
open Engine Engine.Sync
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]
def sealForOld (K : Keys) (cid : Id) (p : B) : m (Option B) := do
  let some (sk, _) ← sessionKeys cid | return none
  let n := (← Fresh.fresh).extract 0 24
  return some (Frame.seal K cid sk n p)
theorem sealForOld_opens [Fresh (HeldM F)] (t : Trust.NativeCrypto) {cid p f : B} {h : Held F}
    (hp : p.size < Crypto.maxPlaintext)
    (hs : ((sealForOld sodium cid p : HeldM F _) h).1 = some f) :
    ∃ sk rk, ((sessionKeys cid : HeldM F _) h).1 = some (sk, rk) ∧
      Frame.open sodium sk f = some (cid, p) := by
  unfold sealForOld at hs
  simp only [HeldM.bind_apply, sessionKeys_reads] at hs
  cases hk : ((sessionKeys cid : HeldM F _) h).1 with
  | none => rw [hk] at hs; cases hs
  | some kk =>
    obtain ⟨sk, rk⟩ := kk
    rw [hk] at hs
    simp only [HeldM.bind_apply, HeldM.pure_apply, Option.some.injEq] at hs
    subst hs
    exact ⟨sk, rk, rfl, open_seal_sodium t ⟨cid, rfl⟩ ⟨sk, rfl⟩ ⟨_, rfl⟩ hp⟩
end Connection
""", 'sealForOld_opens'),
    ('a post sealed with another community bound in', """import app.community.Proofs
namespace Community
open Engine
def sealedPostBad (c adm : Id) (by_ : Device) (k : Key32) (nonce : Nonce24) (text : ByteArray) (n time : Nat)
    (clump : Option Id := none) : Op :=
  let kid := kidOf cryptoSeal k
  post c adm by_ kid (nonce.1 ++ sealBody cryptoSeal k nonce adm kid text) n time clump
theorem sealedPostBad_opens (t : Trust.NativeCrypto) (c adm : Id) (d : Device) (k : Key32) (nonce : Nonce24)
    (text : ByteArray) (n time : Nat) (clump : Option Id)
    (hc : c.size = 32) (ht : text.size < Crypto.maxPlaintext) :
    ∃ kid sealed sg, (Codec.decode (sealedPostBad c adm d k nonce text n time clump).body : Option Body) =
      some (.post kid sealed n time sg) ∧ kid = kidOf cryptoSeal k ∧
      openStored cryptoSeal c kid sealed k.1 = some text := by
  refine ⟨_, _, _, body_mkOp _ _, rfl, ?_⟩
  have G := cryptoSeal_good t
  unfold openStored
  rw [Bytes.of?_val, Option.bind_some]
  exact openSealed_seal G k nonce ht
    (by rw [bodyAd_size hc (show (kidOf cryptoSeal k).size = 32 from G.hash_size _)]; decide)
end Community
""", 'sealedPostBad_opens'),
    ("a wrap to the approver's own key", """import app.community.Proofs
namespace Community
open Engine
def wrapKeyBad (c myAdm toAdm : Id) (d : Device) (k esk : Key32) (_to : ByteArray) : Op :=
  wrap c myAdm toAdm d (box cryptoSeal esk (cryptoSeal.pub esk) (kidOf cryptoSeal k) k)
theorem wrapKeyBad_opens (t : Trust.NativeCrypto) (c myAdm toAdm : Id) (d : Device) (k esk rsk : Key32) :
    ∃ bx sg, (Codec.decode (wrapKeyBad c myAdm toAdm d k esk (cryptoSeal.pub rsk)).body : Option Body) =
      some (.wrap bx sg) ∧ unbox cryptoSeal rsk (kidOf cryptoSeal k) bx = some k := by
  have G := cryptoSeal_good t
  refine ⟨_, _, body_mkOp _ _, unbox_box G rsk esk k _ ?_⟩
  rw [show (kidOf cryptoSeal k).size = 32 from G.hash_size _]; decide
end Community
""", 'wrapKeyBad_opens'),
    ('frames opened under a truncated nonce', """import app.connection.Proofs
namespace Connection
open Engine
def sodiumBad : Keys := { sodium with fdec := fun k n ad c => Noise.xchachaOpen k (n.extract 0 23) ad c }
theorem open_seal_bad (t : Trust.NativeCrypto) (cid : Bytes 32) (sk : Key32) (n : Nonce24) {p : B}
    (hp : p.size < Crypto.maxPlaintext) :
    Frame.open sodiumBad sk.1 (Frame.seal sodiumBad cid.1 sk.1 n.1 p) = some (cid.1, p) :=
  let h := t.xchacha sk n (Frame.ad cid.1) p hp (ad_fits cid)
  open_seal (K := sodiumBad) h.1 h.2 cid.2 n.2
end Connection
""", 'open_seal_bad'),
]:
    code, out = lean(source, 'quiet-mutation-app-')
    errs = [int(m.group(1)) for m in re.finditer(r'Control\.lean:(\d+):\d+: error', out)]
    lo, hi = span(source, target)
    if code == 0 or not errs or not (lo <= errs[0] <= hi):
        raise SystemExit(f'mutation control did not fail at {target}: {label}\n{out[:3000]}')
    print(f'rejected mutation: {label} (fails {target})')
