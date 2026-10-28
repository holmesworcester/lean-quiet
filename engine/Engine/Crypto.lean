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
import Engine.Core

namespace Engine.Crypto

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

end Engine.Crypto
