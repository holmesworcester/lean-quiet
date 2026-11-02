import engine.core.Crypto
import engine.core.Trust
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

Keys and nonces are sized (`Key32`, `Nonce24`): the native code takes no
other size, and code that reads one from storage or the wire checks it
once (`Bytes.of?`), so the laws carry no size premise.

Validators never open anything: they see key ids, nonces and
ciphertexts, and the signatures over them.

Laws, for any suite whose DH commutes and whose AEAD opens what it
seals: `unbox_box` (a device opens a key wrapped to it) and
`openBody_sealBody` (whoever holds the key opens the body). The running
suite `cryptoSeal` is one (`cryptoSeal_good`), given the crates'
correctness (engine/core/Trust.lean).
-/

namespace Community
open Engine

abbrev B := ByteArray

/-- What sealing is built from. Secrets, AEAD keys and nonces are sized. -/
structure Seal where
  /-- X25519: a secret key and a public key to their shared secret. -/
  dh : Key32 → B → B
  pub : Key32 → B
  /-- AEAD: key, nonce, associated data, plaintext. -/
  enc : Key32 → Nonce24 → B → B → B
  dec : Key32 → Nonce24 → B → B → Option B
  hash : B → B

/-- Correctness: key agreement, an AEAD that opens what it seals within
the crate's plaintext and associated-data limits, and 32-byte public keys
and hashes. Key and nonce sizes are in the types. -/
structure Seal.Good (S : Seal) : Prop where
  dh_comm : ∀ a b : Key32, S.dh a (S.pub b) = S.dh b (S.pub a)
  dec_enc : ∀ (k : Key32) (n : Nonce24) ad p, p.size < Crypto.maxPlaintext → ad.size < Crypto.maxAD →
    S.dec k n ad (S.enc k n ad p) = some p
  pub_size : ∀ a, (S.pub a).size = 32
  hash_size : ∀ a, (S.hash a).size = 32

section
variable (S : Seal)

/-- A content key's id. -/
def kidOf (k : Key32) : B := S.hash ("quiet/content-key/v1".toUTF8 ++ k.1)

/-- What a sealed body is bound to. -/
def bodyAd (c kid : B) : B := Codec.encode (c, kid)

def sealBody (k : Key32) (n : Nonce24) (c kid p : B) : B := S.enc k n (bodyAd c kid) p

def openBody (k : Key32) (n : Nonce24) (c kid x : B) : Option B := S.dec k n (bodyAd c kid) x

/-- A sealed body as it travels (the nonce, then the ciphertext), opened
with key k; none without the right key. -/
def openSealed (c kid sealed : B) (k : Key32) : Option B :=
  if h : sealed.size < 24 then none
  else openBody S k (Bytes.front sealed (by omega)) c kid (sealed.extract 24 sealed.size)

/-- A sealed body opened with a key as it is stored: none unless the key
is 32 bytes. -/
def openStored (c kid sealed k : B) : Option B := (Bytes.of? k).bind (openSealed S c kid sealed)

def zeros24 : Nonce24 := Bytes.zeros 24

def boxKey (s epk rpk : B) : B := S.hash ("quiet/wrap/v1".toUTF8 ++ s ++ epk ++ rpk)

/-- Key k (id kid) wrapped to the device whose X25519 key is rpk, with
ephemeral secret esk. Empty if the one-time key is not 32 bytes (a
32-byte hash always is). -/
def box (esk : Key32) (rpk kid : B) (k : Key32) : B :=
  let epk := S.pub esk
  match Bytes.of? (boxKey S (S.dh esk rpk) epk rpk) with
  | some bk => epk ++ S.enc bk zeros24 kid k.1
  | none => .empty

/-- A wrap opened with the device's X25519 secret rsk: the 32-byte key it
holds, or none. -/
def unbox (rsk : Key32) (kid b : B) : Option Key32 :=
  if b.size < 32 then none else
  let epk := b.extract 0 32
  match Bytes.of? (boxKey S (S.dh rsk epk) epk (S.pub rsk)) with
  | some bk => (S.dec bk zeros24 kid (b.extract 32 b.size)).bind Bytes.of?
  | none => none

end

section
variable {S : Seal}

/-- **Whoever holds the key opens the body.** -/
theorem openBody_sealBody (G : S.Good) (k : Key32) (n : Nonce24) (c kid p : B)
    (hp : p.size < Crypto.maxPlaintext) (ha : (bodyAd c kid).size < Crypto.maxAD) :
    openBody S k n c kid (sealBody S k n c kid p) = some p := G.dec_enc _ _ _ _ hp ha

theorem boxKey_of (G : S.Good) (s epk rpk : B) :
    Bytes.of? (boxKey S s epk rpk) = some ⟨boxKey S s epk rpk, G.hash_size _⟩ :=
  Bytes.of?_val ⟨_, G.hash_size _⟩

/-- **A device opens a key wrapped to it.** -/
theorem unbox_box (G : S.Good) (rsk esk k : Key32) (kid : B) (hi : kid.size < Crypto.maxAD) :
    unbox S rsk kid (box S esk (S.pub rsk) kid k) = some k := by
  have hp := G.pub_size esk
  have hb : box S esk (S.pub rsk) kid k = S.pub esk ++
      S.enc ⟨boxKey S (S.dh esk (S.pub rsk)) (S.pub esk) (S.pub rsk), G.hash_size _⟩ zeros24 kid k.1 := by
    simp only [box, boxKey_of G]
  have hs : ¬ (box S esk (S.pub rsk) kid k).size < 32 := by rw [hb, ByteArray.size_append, hp]; omega
  have hk : k.1.size < Crypto.maxPlaintext := by rw [k.2]; decide
  unfold unbox
  simp only [hs, ↓reduceIte]
  rw [hb, ByteArray.extract_append_eq_left hp.symm,
    ByteArray.extract_append_eq_right hp.symm (by rw [ByteArray.size_append, hp]),
    G.dh_comm rsk esk, boxKey_of G]
  simp only [G.dec_enc _ zeros24 kid k.1 hk hi, Option.bind_some]
  exact Bytes.of?_val k

end

/-- The engine's: X25519, XChaCha20-Poly1305, SHA-256. -/
def cryptoSeal : Seal where
  dh a b := Crypto.x25519 a.1 b
  pub a := Crypto.x25519Base a.1
  enc k n := Crypto.xchachaSeal k.1 n.1
  dec k n := Crypto.xchachaOpen k.1 n.1
  hash := Engine.sha256

/-- **The running suite is good**, given the crates' correctness: the
crypto trust file's assumptions, on sized inputs. -/
theorem cryptoSeal_good (t : Trust.NativeCrypto) : cryptoSeal.Good where
  dh_comm a b := t.x25519.2 a b
  dec_enc k n ad p hp ha := (t.xchacha k n ad p hp ha).1
  pub_size a := (t.x25519.1 a).1
  hash_size := t.sha256

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

-- Signatures are the engine's Ed25519 (`Engine.Crypto`).
export Engine.Crypto (edKeypair edSign edVerify)

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

/-- What its author writes and signs: the founding device, its node's
key, and the id of the community's content key (`kidOf` of the key the
founder made), which every post is sealed under. -/
structure Body where
  device : ByteArray
  enc : ByteArray
  kid : ByteArray
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 0 (fun x => (x.device, x.enc, x.kid, x.sig)) (fun (p : B × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 0 :: Codec.enc (x.device, x.enc, x.kid, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `admission`, with the community's content key id (the
root's; an admission copies its root's). -/
structure Fact where
  c : Id
  u : Id
  device : Key
  enc : Key
  kid : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 0 (fun x => (x.c, x.u, x.device, x.enc, x.kid)) (fun (p : B × B × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 0 :: Codec.enc (x.c, x.u, x.device, x.enc, x.kid) := rfl

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
