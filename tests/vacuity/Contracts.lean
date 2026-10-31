import tests.engine.Checks
import tests.vacuity.Session
import tests.vacuity.Merkle

namespace Vacuity.Contracts
open Engine Connection.Noise
set_option linter.defProp false

private instance (k : ByteArray) : Decidable (suite.ValidKey k) :=
  inferInstanceAs (Decidable (k.size = 32))
private instance (p : ByteArray) : Decidable (suite.ValidPayload p) :=
  inferInstanceAs (Decidable (p.size < maxPlaintextSize))
private instance (a : ByteArray) : Decidable (suite.ValidAD a) :=
  inferInstanceAs (Decidable (a.size < 2 ^ 64))

def key : ByteArray := ⟨Array.replicate 32 3⟩
def ad : ByteArray := "session transcript".toUTF8
def payload : ByteArray := "nonempty Noise payload".toUTF8

theorem keyValid : suite.ValidKey key := rfl
theorem adValid : suite.ValidAD ad := by decide
theorem payloadValid : suite.ValidPayload payload := by decide

-- The supported-key/payload contract has an inhabited domain. The universal
-- native crypto correctness premise remains explicit, not fabricated by a
-- finite test; the runner independently checks this actual roundtrip.
theorem noiseContract (g : suite.Good) :
    suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload :=
  g.dec_enc key keyValid 0 ad payload adValid payloadValid

def noiseContractCertificate : Option (PLift
    ((suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload) ∧
      (suite.Good → suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload))) :=
  if h : suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload then
    some (PLift.up ⟨h, noiseContract⟩)
  else none

-- Exact relation to the native stream's rounded-up block count after
-- ChaChaPoly has consumed the first block for its authenticator key.
theorem counterBound (n : Nat) : n < maxPlaintextSize ↔ (n + 63) / 64 ≤ 2^32 - 2 := by
  unfold maxPlaintextSize
  omega

-- A regression against reintroducing the old unrestricted AEAD contract.
-- This is NOT a counterexample to the corrected Suite.Good.
def UnrestrictedRoundtrip : Prop := ∀ k n a p,
  suite.dec k n a (suite.enc k n a p) = some p

def rejectsUnrestricted : Option (PLift (¬ UnrestrictedRoundtrip)) :=
  if h : suite.dec .empty 0 ad (suite.enc .empty 0 ad payload) = none then
    some ⟨fun g => by have h' := g .empty 0 ad payload; rw [h] at h'; cases h'⟩
  else none

-- Symbolic operations support every term. All handshake/secrecy fixtures
-- still use these same functions, with concrete distinct roles and payloads.
def symbolicGood : Symbolic.sym.Good := Symbolic.good

def sized (n : Nat) : ByteArray := ⟨Array.replicate n 3⟩
def lengths : List Nat := [0, 1, 31, 32, 33, 64]

def main : IO UInt32 := do
  let t ← Tests.Checks.new
  t.ok "scoped Noise theorem bridge and native roundtrip" noiseContractCertificate.isSome
  t.ok "corrected Noise contract has concrete supported inputs"
    (Decidable.decide (suite.ValidKey key) && Decidable.decide (suite.ValidAD ad) && Decidable.decide (suite.ValidPayload payload))
  t.ok "correct-size Noise key opens what it seals"
    (suite.dec key 0 ad (suite.enc key 0 ad payload) == some payload)
  t.ok "unrestricted old roundtrip contract remains rejected" rejectsUnrestricted.isSome
  -- No enormous allocation: check the exact boundary used by the contract.
  t.ok "plaintext bound matches native remaining-block check"
    (maxPlaintextSize == 274877906817 && (maxPlaintextSize - 1 + 63) / 64 ≤ 4294967294 &&
      !((maxPlaintextSize + 63) / 64 ≤ 4294967294))
  for n in lengths do
    let sk := sized n
    t.ok s!"key validity classifies size {n}" (Decidable.decide (suite.ValidKey sk) == (n == 32))
    if n != 32 then
      t.ok s!"malformed AEAD key size {n} is rejected"
        ((suite.enc sk 0 ad payload).isEmpty && (suite.dec sk 0 ad (suite.enc sk 0 ad payload)).isNone)
    -- x25519Base's intentional 32-zero fallback keeps framing total;
    -- those zeros are rejected by DH, never accepted as a useful key.
    t.ok s!"public output retains 32-byte framing for private size {n}" ((suite.pub sk).size == 32)
    t.ok s!"split_pair holds even for private size {n}"
      (suite.split (suite.pair (suite.pub sk) payload) == some (suite.pub sk, payload))
    if n != 32 then
      t.ok s!"malformed private size {n} maps to rejected zero point"
        (suite.pub sk == ⟨Array.replicate 32 0⟩ && (suite.dh key (suite.pub sk)).isNone)
    for m in lengths do
      let other : ByteArray := ⟨Array.replicate m 11⟩
      let left := suite.dh sk (suite.pub other)
      let right := suite.dh other (suite.pub sk)
      t.ok s!"DH symmetry private sizes {n}/{m}" (left == right)
      t.ok s!"DH accepts exactly supported private sizes {n}/{m}"
        (left.isSome == (n == 32 && m == 32))
  for n in [0, 1, 31, 32, 64, 65, 129] do
    let ks := suite.hkdf (sized n) "input key material".toUTF8
    t.ok s!"HKDF outputs valid keys for chaining input size {n}"
      (Decidable.decide (suite.ValidKey ks.1) && Decidable.decide (suite.ValidKey ks.2))
    t.ok s!"derived HKDF key supports payload roundtrip size {n}"
      (suite.dec ks.2 1 ad (suite.enc ks.2 1 ad payload) == some payload)
  t.ok "hash output is supported associated data" (Decidable.decide (suite.ValidAD (suite.hash payload)))
  for p in [.empty, payload] do
    t.ok "empty and nonempty supported payloads roundtrip"
      (suite.dec key 18446744073709551615 ad (suite.enc key 18446744073709551615 ad p) == some p)
  return ← t.finish "Noise contract domain and native boundary checks"
end Vacuity.Contracts
