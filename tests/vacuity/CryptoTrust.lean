import tests.engine.Checks
import engine.core.Trust
import app.community.Op
import engine.wire.Noise

/-! Each assumption of the crypto trust file (engine/core/Trust.lean), from
both sides.

- **Consistent:** a toy implementation satisfies each shape, in the kernel,
  so no assumption is contradictory and no law is vacuous for that reason.
- **Has content:** a broken implementation of the same shape fails it, in
  the kernel: an AEAD that loses a byte, a key agreement on one's own
  secret, an all-zero public key, a hash that returns its input.
- **Satisfied by the running code:** the executable runs the native crates
  on real inputs (plaintexts across ChaCha20's 64-byte blocks, several keys,
  nonces and associated data) and checks each shape's statement on them.
- **Wrong sizes are refused:** the native crates refuse every key and nonce
  of another size, which is why the shapes take `Key32`/`Nonce24` and why
  no assumption ranges over another size. -/
namespace Vacuity.CryptoTrust
open Engine Engine.Crypto Trust Tests
set_option linter.defProp false

def key : Key32 := ⟨⟨Array.replicate 32 7⟩, rfl⟩
def nonce : Nonce24 := ⟨⟨Array.replicate 24 9⟩, rfl⟩
def other : Key32 := ⟨⟨Array.replicate 32 8⟩, rfl⟩

/-! ## Consistent: a toy of each shape -/

/-- A toy AEAD: a 16-byte zero tag after the plaintext, dropped on open. -/
def toyEnc (_ : Key32) (_ : Nonce24) (_ p : ByteArray) : ByteArray := p ++ (Bytes.zeros 16).1
def toyDec (_ : Key32) (_ : Nonce24) (_ c : ByteArray) : Option ByteArray :=
  if c.size < 16 then none else some (c.extract 0 (c.size - 16))

theorem toyRoundtrip : Roundtrip toyEnc toyDec := by
  intro k n ad p _ _
  have hz := (Bytes.zeros 16).2
  have hs : (p ++ (Bytes.zeros 16).1).size = p.size + 16 := by rw [ByteArray.size_append, hz]
  refine ⟨?_, hs⟩
  unfold toyDec toyEnc
  rw [if_neg (by omega), hs, Nat.add_sub_cancel, ByteArray.extract_append_eq_left rfl]

/-- A toy agreement: a constant nonzero public key, a constant secret. -/
def toyPub (_ : Key32) : ByteArray := ⟨Array.replicate 32 1⟩
def toyDH (_ : Key32) (_ : ByteArray) : ByteArray := (Bytes.zeros 32).1

theorem toyPub_ne : (⟨Array.replicate 32 1⟩ : ByteArray) ≠ (Bytes.zeros 32).1 := by decide +kernel

theorem toyAgree : Agree toyDH toyPub :=
  ⟨fun _ => ⟨by simp [toyPub, ByteArray.size], toyPub_ne⟩, fun _ _ => rfl⟩

def toyHash (_ : ByteArray) : ByteArray := (Bytes.zeros 32).1

theorem toyDigest : DigestSize toyHash := fun _ => (Bytes.zeros 32).2

/-! ## Has content: a broken implementation of each shape fails it -/

/-- An AEAD whose open loses the plaintext's last byte. -/
def lossyDec (k : Key32) (n : Nonce24) (ad c : ByteArray) : Option ByteArray :=
  (toyDec k n ad c).map fun p => p.extract 0 (p.size - 1)

theorem lossyRefused : ¬ Roundtrip toyEnc lossyDec := by
  intro h
  have := (h key nonce .empty ⟨#[1]⟩ (by decide +kernel) (by decide +kernel)).1
  revert this; decide +kernel

/-- An AEAD that drops its tag: no 16 more bytes. -/
def tagless (_ : Key32) (_ : Nonce24) (_ p : ByteArray) : ByteArray := p
def taglessDec (_ : Key32) (_ : Nonce24) (_ c : ByteArray) : Option ByteArray := some c

theorem taglessRefused : ¬ Roundtrip tagless taglessDec := by
  intro h
  have := (h key nonce .empty .empty (by decide +kernel) (by decide +kernel)).2
  revert this; decide +kernel

/-- A key agreement on one's own secret. -/
def ownDH (a : Key32) (_ : ByteArray) : ByteArray := a.1

theorem ownRefused : ¬ Agree ownDH toyPub := by
  intro h
  have := h.2 key other
  revert this; decide +kernel

/-- A public key that is the all-zero point. -/
theorem zeroPubRefused : ¬ Agree toyDH (fun _ => (Bytes.zeros 32).1) := by
  intro h
  exact (h.1 key).2 rfl

/-- A hash that returns its input. -/
theorem idHashRefused : ¬ DigestSize id := by
  intro h
  have := h .empty
  revert this; decide +kernel

/-- The whole trust file, bridged to both running suites: what every
crypto law's instance at running code takes. -/
def nativeConditional := some (PLift.up (fun t : Trust.NativeCrypto =>
  And.intro (Community.cryptoSeal_good t) (Connection.Noise.suite_good t)))

/-! ## Satisfied by the running code: each shape on the native crates -/

def plaintexts : List Nat := [0, 1, 15, 16, 63, 64, 65, 1000, 4096, 70001]
def ads : List ByteArray := [.empty, ⟨Array.replicate 33 5⟩, ⟨Array.replicate 1000 6⟩]

/-- One sample of `XChaCha`'s statement on the native crate. -/
def xchachaAt (k : Key32) (n : Nonce24) (ad p : ByteArray) : Bool :=
  let c := xchachaSeal k.1 n.1 ad p
  xchachaOpen k.1 n.1 ad c == some p && c.size == p.size + 16

def chachaAt (k : Key32) (n : UInt64) (ad p : ByteArray) : Bool :=
  let c := chachaSeal k.1 n ad p
  chachaOpen k.1 n ad c == some p && c.size == p.size + 16

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "the trust file is what both running suites need" nativeConditional.isSome
  let keys : List Key32 := [key, other, Bytes.zeros 32, Bytes.fit 32 ⟨Array.replicate 32 255⟩,
    ← Bytes.expect 32 (← randomBytes 32)]
  let nonces : List Nonce24 := [nonce, Bytes.zeros 24, ← Bytes.expect 24 (← randomBytes 24)]
  for k in keys do
    for n in nonces do
      for ad in ads do
        t.ok s!"XChaCha opens what it seals, 16 bytes longer, ad {ad.size}, plaintexts {plaintexts}"
          (plaintexts.all fun len => xchachaAt k n ad ⟨Array.replicate len 42⟩)
    for n in [0, 1, 18446744073709551615] do
      t.ok s!"ChaCha opens what it seals, nonce {n}"
        (plaintexts.all fun len => ads.all fun ad => chachaAt k (UInt64.ofNat n) ad ⟨Array.replicate len 42⟩)
    t.ok "an X25519 public key is 32 bytes and not the zero point"
      ((x25519Base k.1).size == 32 && x25519Base k.1 != (Bytes.zeros 32).1)
    for k' in keys do
      t.ok "X25519 agrees" (x25519 k.1 (x25519Base k'.1) == x25519 k'.1 (x25519Base k.1))
  for len in [0, 1, 55, 56, 64, 1000, 70001] do
    t.ok s!"a SHA-256 digest of {len} bytes is 32 bytes" ((sha256 ⟨Array.replicate len 3⟩).size == 32)
  -- A different key, nonce or associated data opens nothing: the
  -- assumptions are about this crate, not a cipher that ignores its key.
  let p := "content-bearing plaintext".toUTF8
  let c := xchachaSeal key.1 nonce.1 .empty p
  t.ok "XChaCha: another key opens nothing" (xchachaOpen other.1 nonce.1 .empty c == none)
  t.ok "XChaCha: another nonce opens nothing" (xchachaOpen key.1 (Bytes.zeros 24).1 .empty c == none)
  t.ok "XChaCha: other associated data opens nothing" (xchachaOpen key.1 nonce.1 ⟨#[1]⟩ c == none)
  let damaged : ByteArray := ⟨c.data.modify 3 fun b => b ^^^ 1⟩
  t.ok "XChaCha: a same-size tampered ciphertext opens nothing" (xchachaOpen key.1 nonce.1 .empty damaged == none)
  -- Wrong sizes: what the shapes' Key32/Nonce24 exclude.
  for size in [0, 1, 16, 31, 33, 64] do
    let bad : ByteArray := ⟨Array.replicate size 7⟩
    t.ok s!"XChaCha refuses a {size}-byte key"
      ((xchachaSeal bad nonce.1 .empty p).isEmpty && xchachaOpen bad nonce.1 .empty c == none)
    t.ok s!"ChaCha refuses a {size}-byte key" (chachaOpen bad 0 .empty (chachaSeal key.1 0 .empty p) == none)
    t.ok s!"X25519 gives no shared secret for a {size}-byte secret" ((x25519 bad (x25519Base key.1)).isEmpty)
    t.ok s!"Bytes.of? refuses {size} bytes as a key" (Bytes.of? (n := 32) bad).isNone
  for size in [0, 1, 12, 23, 25, 32] do
    let bad : ByteArray := ⟨Array.replicate size 9⟩
    t.ok s!"XChaCha refuses a {size}-byte nonce"
      ((xchachaSeal key.1 bad .empty p).isEmpty && xchachaOpen key.1 bad .empty c == none)
    t.ok s!"Bytes.of? refuses {size} bytes as a nonce" (Bytes.of? (n := 24) bad).isNone
  t.finish "crypto trust file: satisfied by the native crates, wrong sizes refused"

end Vacuity.CryptoTrust
