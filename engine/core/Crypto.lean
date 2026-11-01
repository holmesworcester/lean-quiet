/-
The engine's crypto primitives, for every family: X25519, the AEADs
(IETF ChaCha20-Poly1305 with a counter nonce, XChaCha20-Poly1305 with a
random 24-byte nonce), the Ed25519 → X25519 key conversion, and the OS's
random bytes. They come from libquiet's Rust crates through native/crypto
(native/crypto.c). SHA-256 is in Engine.Core.

The laws that use them take them as parameters (DH commutes, an AEAD
opens what it seals), so the laws hold for any implementation and the
tests check this one.
-/
import engine.core.Core

namespace Engine

/-- Bytes of exactly `n`: a key or a nonce whose size its type carries.
The native AEADs and X25519 refuse any other size, so a law over these
has no size premise, and each call site discharges it by construction:
`Bytes.of?` checks bytes read from storage or the wire, `Bytes.front`
slices a longer array. -/
abbrev Bytes (n : Nat) := { b : ByteArray // b.size = n }

/-- A 32-byte key: X25519 secrets, AEAD keys. -/
abbrev Key32 := Bytes 32
/-- A 24-byte XChaCha20-Poly1305 nonce. -/
abbrev Nonce24 := Bytes 24

namespace Bytes

/-- `b` as `n` bytes, if it holds exactly that many. -/
def of? {n : Nat} (b : ByteArray) : Option (Bytes n) := if h : b.size = n then some ⟨b, h⟩ else none

theorem of?_val {n : Nat} (k : Bytes n) : of? (n := n) k.1 = some k := by
  unfold of?; simp [k.2]

theorem of?_eq_some {n : Nat} {b : ByteArray} {k : Bytes n} (h : of? (n := n) b = some k) : k.1 = b := by
  unfold of? at h; split at h <;> cases h; rfl

theorem of?_none {n : Nat} {b : ByteArray} (h : b.size ≠ n) : of? (n := n) b = none := by
  unfold of?; simp [h]

/-- The first `n` bytes of `b`, which holds at least that many. -/
def front {n : Nat} (b : ByteArray) (h : n ≤ b.size) : Bytes n :=
  ⟨b.extract 0 n, by rw [ByteArray.size_extract]; omega⟩

/-- `n` zero bytes. -/
def zeros (n : Nat) : Bytes n := ⟨⟨Array.replicate n 0⟩, by simp [ByteArray.size]⟩

/-- The first `n` bytes of `b`, zero-padded if it holds fewer: fixtures'
keys and nonces, derived from a digest (SHA-256's is 32 bytes, so a
32-byte or shorter one is never padded). -/
def fit (n : Nat) (b : ByteArray) : Bytes n :=
  ⟨(b ++ (zeros n).1).extract 0 n, by
    simp only [ByteArray.size_extract, ByteArray.size_append, (zeros n).2]; omega⟩

/-- `b`, which a caller asked for `n` of (the OS's randomness), as `n`
bytes; an error if it holds another size. -/
def expect (n : Nat) (b : ByteArray) : IO (Bytes n) :=
  match of? b with
  | some k => pure k
  | none => throw (IO.userError s!"wanted {n} bytes, got {b.size}")

/-- A 32-byte key derived from bytes, by hashing: for fixtures. -/
def digest (b : ByteArray) : Bytes 32 := fit 32 (sha256 b)

end Bytes

end Engine

namespace Engine.Crypto

/-- Exclusive plaintext limit of the native ChaCha20 stream, for both
AEADs. RustCrypto's AEAD reserves block zero for Poly1305, and the stream
then permits at most `u32::MAX - 1` complete or partial blocks:
`ceil(len / 64) <= 2^32 - 2`. This is stricter than the outer AEAD's
floor-division check. -/
def maxPlaintext : Nat := 64 * (2 ^ 32 - 2) + 1

/-- Exclusive associated-data limit: Poly1305 authenticates its length
as an unsigned 64-bit integer. -/
def maxAD : Nat := 2 ^ 64

@[extern "le_x25519"] opaque x25519 (sk pk : @& ByteArray) : ByteArray
@[extern "le_x25519_base"] opaque x25519Base (sk : @& ByteArray) : ByteArray
@[extern "le_chachapoly_seal"] opaque chachaSeal (k : @& ByteArray) (n : UInt64) (ad p : @& ByteArray) :
  ByteArray
@[extern "le_chachapoly_open"] opaque chachaOpen (k : @& ByteArray) (n : UInt64) (ad c : @& ByteArray) :
  Option ByteArray
/-- A device's X25519 secret, from its Ed25519 secret key (seed ++ pk). -/
@[extern "le_ed_sk_to_x"] opaque staticOf (edSk : @& ByteArray) : ByteArray
/-- A device's X25519 key, from its Ed25519 key; empty if not a point. -/
@[extern "le_ed_pk_to_x"] opaque staticPubOf (edPk : @& ByteArray) : ByteArray
/-- XChaCha20-Poly1305: key, 24-byte nonce, associated data, plaintext. -/
@[extern "le_xchacha_seal"] opaque xchachaSeal (k n ad p : @& ByteArray) : ByteArray
@[extern "le_xchacha_open"] opaque xchachaOpen (k n ad c : @& ByteArray) : Option ByteArray
/-- Random bytes from the OS. -/
@[extern "le_random"] opaque randomBytes (n : UInt32) : IO ByteArray
/-- Ed25519: a 64-byte key pair (public, then secret) from a 32-byte seed. -/
@[extern "le_ed25519_keypair"] opaque edKeypair (seed : @& ByteArray) : ByteArray
/-- Ed25519: the signature of a message under a secret key. -/
@[extern "le_ed25519_sign"] opaque edSign (sk msg : @& ByteArray) : ByteArray
/-- Ed25519: whether a signature verifies under a public key. -/
@[extern "le_ed25519_verify"] opaque edVerify (pk msg sig : @& ByteArray) : Bool

end Engine.Crypto
