/-
**What the proofs trust about the crypto, in one place.** This is the
crypto area's trust file. Each assumption is a named `Prop`, never an
`axiom`: a law that needs one takes it as a premise, so `#print axioms`
stays at Lean's three and the premise tables tag it `[crypto]`.

Each one is tested from both sides (tests/vacuity/CryptoTrust.lean):
- the running code satisfies it: the native crates, at the supported
  sizes, on concrete inputs;
- a degenerate model fails it: a broken suite of the same shape.

Sizes are not trusted. Keys and nonces are `Bytes 32` and `Bytes 24`
(engine/core/Crypto.lean), the only sizes the native code accepts, so no
assumption ranges over a size it refuses. The plaintext and
associated-data bounds are the crate's own limits.

These are correctness properties of the implementations, not security:
secrecy is the symbolic model's (engine/wire/NoiseSymbolic.lean), and
signatures and hashes have their own assumptions (`Community.Unforgeable`,
`Merkle.NoCollision`).
-/
import engine.core.Crypto

namespace Trust
open Engine Engine.Crypto

/-! ## The shapes, for any implementation -/

/-- An AEAD opens what it seals: under a 32-byte key and any nonce, a
supported plaintext and associated data seal to 16 more bytes (the tag),
which open back to the plaintext. -/
def Roundtrip {N : Type} (enc : Key32 → N → ByteArray → ByteArray → ByteArray)
    (dec : Key32 → N → ByteArray → ByteArray → Option ByteArray) : Prop :=
  ∀ (k : Key32) (n : N) (ad p : ByteArray), p.size < maxPlaintext → ad.size < maxAD →
    dec k n ad (enc k n ad p) = some p ∧ (enc k n ad p).size = p.size + 16

/-- A key agreement agrees: a 32-byte secret's public key is 32 bytes and
not the all-zero point, and two secrets reach one shared secret through
each other's public keys. -/
def Agree (dh : Key32 → ByteArray → ByteArray) (pub : Key32 → ByteArray) : Prop :=
  (∀ a : Key32, (pub a).size = 32 ∧ pub a ≠ (Bytes.zeros 32).1) ∧ ∀ a b : Key32, dh a (pub b) = dh b (pub a)

/-- A hash's digests are 32 bytes. -/
def DigestSize (h : ByteArray → ByteArray) : Prop := ∀ b : ByteArray, (h b).size = 32

/-! ## The running crates' -/

/-- **XChaCha20-Poly1305 opens what it seals** (chacha20poly1305 0.11,
24-byte nonce): the sealed bodies, wraps, files and frames. -/
def XChaCha : Prop := Roundtrip (fun k (n : Nonce24) => xchachaSeal k.1 n.1) (fun k n => xchachaOpen k.1 n.1)

/-- **ChaCha20-Poly1305 opens what it seals** (the same crate, IETF
variant, Noise's counter nonce): the handshake payloads. -/
def ChaCha : Prop := Roundtrip (fun k (n : UInt64) => chachaSeal k.1 n) (fun k n => chachaOpen k.1 n)

/-- **X25519 agrees** (curve25519-dalek). -/
def X25519 : Prop := Agree (fun a b => x25519 a.1 b) (fun a => x25519Base a.1)

/-- **A SHA-256 digest is 32 bytes** (sha2). -/
def Sha256Size : Prop := DigestSize sha256

/-- All four: what a suite built on the native crates needs. -/
structure Native : Prop where
  xchacha : XChaCha
  chacha : ChaCha
  x25519 : X25519
  sha256 : Sha256Size

end Trust
