import tests.engine.Checks
import tests.vacuity.Session
import tests.vacuity.Merkle
import app.community.Proofs

namespace Vacuity.Contracts
open Engine Connection.Noise
set_option linter.defProp false

private instance (k : ByteArray) : Decidable (suite.ValidKey k) :=
  inferInstanceAs (Decidable (k.size = 32))
private instance (p : ByteArray) : Decidable (suite.ValidPayload p) :=
  inferInstanceAs (Decidable (p.size < Crypto.maxPlaintext))
private instance (a : ByteArray) : Decidable (suite.ValidAD a) :=
  inferInstanceAs (Decidable (a.size < Crypto.maxAD))

def key : ByteArray := ⟨Array.replicate 32 3⟩
def ad : ByteArray := "session transcript".toUTF8
def payload : ByteArray := "nonempty Noise payload".toUTF8

theorem keyValid : suite.ValidKey key := rfl
theorem adValid : suite.ValidAD ad := by decide
theorem payloadValid : suite.ValidPayload payload := by decide

-- The supported-key/payload contract has an inhabited domain. The running
-- suite is good given the crypto trust file (`suite_good`); the runner
-- independently checks this actual roundtrip.
theorem noiseContract (t : Trust.Native) :
    suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload :=
  (suite_good t).dec_enc key keyValid 0 ad payload adValid payloadValid

def noiseContractCertificate : Option (PLift
    ((suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload) ∧
      (Trust.Native → suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload))) :=
  if h : suite.dec key 0 ad (suite.enc key 0 ad payload) = some payload then
    some (PLift.up ⟨h, noiseContract⟩)
  else none

/-- The running Noise suite is good, given the crypto trust file. -/
def suiteGoodConditional := some (PLift.up (fun t : Trust.Native => suite_good t))

-- Exact relation to the native stream's rounded-up block count after
-- ChaChaPoly has consumed the first block for its authenticator key.
theorem counterBound (n : Nat) : n < Crypto.maxPlaintext ↔ (n + 63) / 64 ≤ 2^32 - 2 := by
  unfold Crypto.maxPlaintext
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
  t.ok "trust file bridged to the running Noise suite" suiteGoodConditional.isSome
  t.ok "corrected Noise contract has concrete supported inputs"
    (Decidable.decide (suite.ValidKey key) && Decidable.decide (suite.ValidAD ad) && Decidable.decide (suite.ValidPayload payload))
  t.ok "correct-size Noise key opens what it seals"
    (suite.dec key 0 ad (suite.enc key 0 ad payload) == some payload)
  t.ok "unrestricted old roundtrip contract remains rejected" rejectsUnrestricted.isSome
  -- No enormous allocation: check the exact boundary used by the contract.
  t.ok "plaintext bound matches native remaining-block check"
    (Crypto.maxPlaintext == 274877906817 && (Crypto.maxPlaintext - 1 + 63) / 64 ≤ 4294967294 &&
      !((Crypto.maxPlaintext + 63) / 64 ≤ 4294967294))
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
/-! ## Unforgeability, scoped to a store

A toy scheme with a valid signature for every message under every key
(the signature is the key itself): forgeries exist, as they do for
Ed25519, and only a store can be free of them. `Community.Unforgeable`
holds of a store holding one signed op, with `Signed` true of that op's
signed bytes only; the unscoped form fails for the same `Signed`. -/

def toyCrypto : Community.Crypto := { verify := fun pk _ s => decide (s = pk), pub := id }
def toyKey : ByteArray := ⟨#[7]⟩
def toyOp : Op := Community.mkOp [] (.grant toyKey)
def toyStore (x : Id) : Option Op := if x = toyOp.id then some toyOp else none
def toyMsg : ByteArray := Community.signed toyOp (.grant toyKey)
def ToySigned (pk m : ByteArray) : Prop := pk = toyKey ∧ m = toyMsg

theorem unforgeableScoped :
    Community.Unforgeable toyCrypto toyStore ToySigned ∧
    (∀ pk m, ∃ s, toyCrypto.verify pk m s = true) ∧
    ¬ ToySigned toyKey (toyMsg ++ ⟨#[0]⟩) ∧
    ¬ (∀ pk m s, toyCrypto.verify pk m s = true → ToySigned pk m) := by
  refine ⟨?_, fun pk _ => ⟨pk, by simp [toyCrypto]⟩, ?_, ?_⟩
  · intro x o b pk s hx hb hs hv
    unfold toyStore at hx
    split at hx
    · cases hx
      have hb' : (Codec.decode toyOp.body : Option Community.Body) = some (.grant toyKey) :=
        Codec.decode_encode _
      rw [hb'] at hb
      cases hb
      simp only [Community.Body.sigs, List.mem_singleton] at hs
      subst hs
      simp only [toyCrypto, decide_eq_true_eq] at hv
      exact ⟨hv.symm, rfl⟩
    · cases hx
  · rintro ⟨_, h⟩
    have := congrArg ByteArray.size h
    simp [ByteArray.size_append] at this
    exact absurd (congrArg ByteArray.size this) (by decide)
  · intro h
    have := congrArg ByteArray.size (h toyKey (toyMsg ++ ⟨#[0]⟩) toyKey (by simp [toyCrypto])).2
    simp [ByteArray.size_append] at this
    exact absurd (congrArg ByteArray.size this) (by decide)

/-- The unscoped form under the same scheme forces `Signed` everywhere on
the key: why `Unforgeable` ranges over a store. -/
theorem unscopedForces (Signed : ByteArray → ByteArray → Prop)
    (hU : ∀ pk m s, toyCrypto.verify pk m s = true → Signed pk m) (m : ByteArray) :
    Signed toyKey m :=
  Community.unscoped_signs_all (C := toyCrypto) hU (fun _ => ⟨toyKey, by simp [toyCrypto]⟩) m

end Vacuity.Contracts
