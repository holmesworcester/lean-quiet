/-
Content keys: how a community's bodies are sealed, and how a content
key reaches a device. This is libquiet's BodyProtection, made
structural: an op's body says which fields are sealed.
- **The key.** A content key K is 32 random bytes, named by its id
  `kidOf K`, a hash of it. The id travels; K never does, except wrapped.
- **Sealing a body.** XChaCha20-Poly1305 under K with a random 24-byte
  nonce. The associated data binds it to its community and key id, so a
  sealed body cannot be moved into another community's op.
- **A wrap.** It seals K to one device's X25519 key. A fresh ephemeral
  key pair is drawn. Its shared secret with the device, hashed with both
  public keys, is a one-time key, and K is sealed under it. The nonce is
  zero because the key is used once. The device opens it with its X25519
  secret.

Validators never open anything: they see key ids, nonces and
ciphertexts, and the signatures over them.

Laws, for any suite whose DH commutes and whose AEAD opens what it
seals: `unbox_box` (a device opens a key wrapped to it) and
`openBody_sealBody` (whoever holds the key opens the body).
-/
import engine.core.Crypto

namespace Community
open Engine

abbrev B := ByteArray

/-- What sealing is built from. -/
structure Seal where
  /-- X25519: a secret key and a public key to their shared secret. -/
  dh : B → B → B
  pub : B → B
  /-- AEAD: key, 24-byte nonce, associated data, plaintext. -/
  enc : B → B → B → B → B
  dec : B → B → B → B → Option B
  hash : B → B

structure Seal.Good (S : Seal) : Prop where
  dh_comm : ∀ a b, S.dh a (S.pub b) = S.dh b (S.pub a)
  dec_enc : ∀ k n ad p, S.dec k n ad (S.enc k n ad p) = some p
  pub_size : ∀ a, (S.pub a).size = 32

section
variable (S : Seal)

/-- A content key's id. -/
def kidOf (k : B) : B := S.hash ("quiet/content-key/v1".toUTF8 ++ k)

/-- What a sealed body is bound to. -/
def bodyAd (c kid : B) : B := Codec.encode (c, kid)

def sealBody (k n c kid p : B) : B := S.enc k n (bodyAd c kid) p

def openBody (k n c kid x : B) : Option B := S.dec k n (bodyAd c kid) x

/-- A sealed body as it travels (the nonce, then the ciphertext), opened
with key k; none without the right key. -/
def openSealed (c kid sealed k : B) : Option B :=
  if sealed.size < 24 then none
  else openBody S k (sealed.extract 0 24) c kid (sealed.extract 24 sealed.size)

def zeros24 : B := ⟨Array.replicate 24 0⟩

def boxKey (s epk rpk : B) : B := S.hash ("quiet/wrap/v1".toUTF8 ++ s ++ epk ++ rpk)

/-- Key k (id kid) wrapped to the device whose X25519 key is rpk, with
ephemeral secret esk. -/
def box (esk rpk kid k : B) : B :=
  let epk := S.pub esk
  epk ++ S.enc (boxKey S (S.dh esk rpk) epk rpk) zeros24 kid k

/-- A wrap opened with the device's X25519 secret rsk. -/
def unbox (rsk kid b : B) : Option B :=
  if b.size < 32 then none else
  let epk := b.extract 0 32
  S.dec (boxKey S (S.dh rsk epk) epk (S.pub rsk)) zeros24 kid (b.extract 32 b.size)

end

section
variable {S : Seal}

/-- **Whoever holds the key opens the body.** -/
theorem openBody_sealBody (G : S.Good) (k n c kid p : B) :
    openBody S k n c kid (sealBody S k n c kid p) = some p := G.dec_enc _ _ _ _

/-- **A device opens a key wrapped to it.** -/
theorem unbox_box (G : S.Good) (rsk esk kid k : B) :
    unbox S rsk kid (box S esk (S.pub rsk) kid k) = some k := by
  have hp := G.pub_size esk
  have hs : ¬ (S.pub esk ++ S.enc (boxKey S (S.dh esk (S.pub rsk)) (S.pub esk) (S.pub rsk)) zeros24 kid k).size
      < 32 := by rw [ByteArray.size_append, hp]; omega
  unfold unbox box
  simp only [hs, ↓reduceIte]
  rw [ByteArray.extract_append_eq_left hp.symm,
    ByteArray.extract_append_eq_right hp.symm (by rw [ByteArray.size_append, hp]),
    G.dh_comm rsk esk, G.dec_enc]

end

/-- The engine's: X25519, XChaCha20-Poly1305, SHA-256. -/
def cryptoSeal : Seal where
  dh := Crypto.x25519
  pub := Crypto.x25519Base
  enc := Crypto.xchachaSeal
  dec := Crypto.xchachaOpen
  hash := Engine.sha256

end Community
