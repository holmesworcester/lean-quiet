import engine.core.Crypto
import engine.core.Engine

section

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

/-- Exclusive plaintext limit after RustCrypto's AEAD reserves block zero
for Poly1305. The stream cipher then permits at most `u32::MAX - 1`
complete or partial blocks: `ceil(len / 64) <= 2^32 - 2`. This is stricter
than the outer AEAD's floor-division check and applies to XChaCha too. -/
def Seal.maxPlaintextSize : Nat := 64 * (2^32 - 2) + 1

/-- AEAD authenticates the associated-data length as an unsigned 64-bit
integer. Native arrays on supported hosts fit; the logical contract also
states the bound for its unrestricted `ByteArray` quantifier. -/
def Seal.maxAssociatedDataSize : Nat := 2^64

/-- Correctness on the native primitives' supported inputs. Key agreement
uses 32-byte private keys; XChaCha uses a 32-byte key and 24-byte nonce.
Its plaintext must fit the counter range. Hash output size supplies the
AEAD key-size premise for wrapping. -/
structure Seal.Good (S : Seal) : Prop where
  dh_comm : ∀ a b, a.size = 32 → b.size = 32 → S.dh a (S.pub b) = S.dh b (S.pub a)
  dec_enc : ∀ k n ad p, k.size = 32 → n.size = 24 → p.size < Seal.maxPlaintextSize →
    ad.size < Seal.maxAssociatedDataSize →
    S.dec k n ad (S.enc k n ad p) = some p
  pub_size : ∀ a, (S.pub a).size = 32
  hash_size : ∀ a, (S.hash a).size = 32

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
theorem openBody_sealBody (G : S.Good) (k n c kid p : B)
    (hk : k.size = 32) (hn : n.size = 24) (hp : p.size < Seal.maxPlaintextSize)
    (ha : (bodyAd c kid).size < Seal.maxAssociatedDataSize) :
    openBody S k n c kid (sealBody S k n c kid p) = some p := G.dec_enc _ _ _ _ hk hn hp ha

/-- **A device opens a key wrapped to it.** -/
theorem unbox_box (G : S.Good) (rsk esk kid k : B) (hr : rsk.size = 32) (he : esk.size = 32)
    (hk : k.size < Seal.maxPlaintextSize) (hi : kid.size < Seal.maxAssociatedDataSize) :
    unbox S rsk kid (box S esk (S.pub rsk) kid k) = some k := by
  have hp := G.pub_size esk
  have hs : ¬ (S.pub esk ++ S.enc (boxKey S (S.dh esk (S.pub rsk)) (S.pub esk) (S.pub rsk)) zeros24 kid k).size
      < 32 := by rw [ByteArray.size_append, hp]; omega
  unfold unbox box
  simp only [hs, ↓reduceIte]
  rw [ByteArray.extract_append_eq_left hp.symm,
    ByteArray.extract_append_eq_right hp.symm (by rw [ByteArray.size_append, hp]),
    G.dh_comm rsk esk hr he]
  exact G.dec_enc _ zeros24 kid k (G.hash_size _) (by decide) hk hi

end

/-- The engine's: X25519, XChaCha20-Poly1305, SHA-256. -/
def cryptoSeal : Seal where
  dh := Crypto.x25519
  pub := Crypto.x25519Base
  enc := Crypto.xchachaSeal
  dec := Crypto.xchachaOpen
  hash := Engine.sha256

end Community

end

section

/-
The community family's root op, and what every op of the family cites:
the signature scheme (`Crypto`, a parameter, so the laws hold for any
scheme), what a signature covers (`signedBy`), and the numbers sort keys
are made of. Every op folder below this one imports it.
-/

namespace Community
open Engine Codec

abbrev Key := ByteArray

structure Crypto where
  verify : Key → ByteArray → ByteArray → Bool
  /-- The public key a 32-byte seed's key pair has. -/
  pub : ByteArray → Key

def decAs {α β} [Codec α] (f : α → β) (bs : List UInt8) : Option (β × List UInt8) :=
  match (dec bs : Option (α × List UInt8)) with
  | none => none
  | some (a, r) => some (f a, r)

theorem decAs_enc {α β} [Codec α] (f : α → β) (a : α) (rest : List UInt8) :
    decAs f (enc a ++ rest) = some (f a, rest) := by
  unfold decAs; rw [Codec.round]

/-- The counter cap: a post claiming this or more is saturated, and is
ordered by this device's receipt of it (`received`). Below 2^64, so a
counter and the cap fit the 8 bytes a sort key gives them. -/
def countCap : Nat := 2 ^ 63

/-- A number as 8 bytes, most significant first, so byte order is
numeric order. -/
def be64 (n : Nat) : ByteArray := ByteArray.mk ((List.range 8).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray

/-- The largest time a sort key tells apart: later claims sort as it. -/
def timeCap : Nat := 2 ^ 64 - 1

/-- The bytes a signature on an op covers: a domain tag, the op's
requirements (its community first) and its unsigned body. -/
def signedBy {β} [Codec β] (o : Op) (b : β) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, o.reqs, b)

/-! ## The root: it founds a community -/

/- The root founds the community; its fact is the founder's admission,
and the founder's user is the community id. The founder is admin. -/
namespace Root

/-- What its author writes and signs. -/
structure Body where
  device : ByteArray
  enc : ByteArray
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 0 (fun x => (x.device, x.enc, x.sig)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 0 :: Codec.enc (x.device, x.enc, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `admission`. -/
structure Fact where
  c : Id
  u : Id
  device : Key
  enc : Key
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 0 (fun x => (x.c, x.u, x.device, x.enc)) (fun (p : B × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 0 :: Codec.enc (x.c, x.u, x.device, x.enc) := rfl

/-! ## The lists its fact is filed in (`admission.*`) -/
/-- A device's admissions: whom `allowPeer` asks about. -/
def byDevice : Rel Fact := ⟨"admission", "byDevice", fun f => some [f.c, f.device]⟩
@[simp] theorem byDevice_args (f : Fact) : byDevice.args f = (some [f.c, f.device]) := rfl
/-- A community's admissions: whom to dial and seal to. -/
def all : Rel Fact := ⟨"admission", "all", fun f => some [f.c]⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some [f.c]) := rfl
/-- A user's admissions (its devices): whom a removal cites. -/
def byUser : Rel Fact := ⟨"admission", "byUser", fun f => some [f.c, f.u]⟩
@[simp] theorem byUser_args (f : Fact) : byUser.args f = (some [f.c, f.u]) := rfl
/-- The admissions naming an X25519 key: the devices a node's key
speaks for in c, which `allowPeer` asks about. -/
def byKey : Rel Fact := ⟨"admission", "byKey", fun f => some [f.c, f.enc]⟩
@[simp] theorem byKey_args (f : Fact) : byKey.args f = (some [f.c, f.enc]) := rfl

end Root

end Community

end
