import tests.engine.Lib

/-! The production contract covers the native input domain: 32-byte AEAD and
private keys, 24-byte nonces, and plaintext within the ChaCha counter range.
The size premises below are kernel proofs; actual cryptographic equalities
are checked by native executable certificates. They exercise finite inputs,
not a proof of the universally quantified native cryptoSeal.Good assumption.
Malformed-input regressions still refute the former unrestricted AEAD law. -/
namespace Vacuity.SealAudit
open Engine Community Tests
set_option linter.defProp false

def key : ByteArray := ⟨Array.replicate 32 7⟩
def nonce : ByteArray := ⟨Array.replicate 24 9⟩
def room : ByteArray := ⟨Array.replicate 32 11⟩
def text := "Hello Bob, this is an encrypted test message.".toUTF8
def ad := "quiet-vacuity-associated-data".toUTF8
def rsk : ByteArray := ⟨Array.replicate 32 13⟩
def esk : ByteArray := ⟨Array.replicate 32 17⟩
def kid := kidOf cryptoSeal key

theorem keySize : key.size = 32 := by decide +kernel
theorem nonceSize : nonce.size = 24 := by decide +kernel
theorem recipientSize : rsk.size = 32 := by decide +kernel
theorem ephemeralSize : esk.size = 32 := by decide +kernel
theorem textFits : text.size < Seal.maxPlaintextSize := by decide +kernel
theorem keyFits : key.size < Seal.maxPlaintextSize := by decide +kernel
theorem adFits : ad.size < Seal.maxAssociatedDataSize := by decide +kernel

-- The strict bound is precisely the native counter check, including its
-- endpoint. This proves the boundary arithmetically without a 256 GiB buffer.
theorem counterBound (n : Nat) : n < Seal.maxPlaintextSize ↔ n / 64 < 2^32 - 1 := by
  unfold Seal.maxPlaintextSize
  omega

def wrappingKey := boxKey cryptoSeal (cryptoSeal.dh esk (cryptoSeal.pub rsk))
  (cryptoSeal.pub esk) (cryptoSeal.pub rsk)

def samplePremises : Option (PLift (
    cryptoSeal.dh rsk (cryptoSeal.pub esk) = cryptoSeal.dh esk (cryptoSeal.pub rsk) ∧
    cryptoSeal.dec key nonce ad (cryptoSeal.enc key nonce ad text) = some text ∧
    (cryptoSeal.pub esk).size = 32 ∧ wrappingKey.size = 32 ∧
    cryptoSeal.dec wrappingKey zeros24 kid (cryptoSeal.enc wrappingKey zeros24 kid key) = some key)) :=
  if h : cryptoSeal.dh rsk (cryptoSeal.pub esk) = cryptoSeal.dh esk (cryptoSeal.pub rsk) ∧
    cryptoSeal.dec key nonce ad (cryptoSeal.enc key nonce ad text) = some text ∧
    (cryptoSeal.pub esk).size = 32 ∧ wrappingKey.size = 32 ∧
    cryptoSeal.dec wrappingKey zeros24 kid (cryptoSeal.enc wrappingKey zeros24 kid key) = some key then
    some ⟨h⟩
  else none

-- The actual contract supplies these concrete facts, conditionally. The
-- executable independently checks every equality in samplePremises above.
def goodConditional := some (PLift.up (fun good : cryptoSeal.Good =>
  And.intro (good.dh_comm rsk esk recipientSize ephemeralSize)
    (And.intro (good.dec_enc key nonce ad text keySize nonceSize textFits adFits)
      (And.intro (good.pub_size esk) (good.hash_size ad)))))

def openSealedConditional :=
  if ha : (bodyAd room kid).size < Seal.maxAssociatedDataSize then
    some (PLift.up (fun good : cryptoSeal.Good =>
      openSealed_seal (c := room) (kid := kid) (k := key) (n := nonce) (text := text)
        good keySize nonceSize textFits ha))
  else none

def memberOpensConditional :=
  if ha : (bodyAd room kid).size < Seal.maxAssociatedDataSize then
    some (PLift.up (fun good : cryptoSeal.Good =>
      member_opens good rsk esk key nonce room text recipientSize ephemeralSize keySize nonceSize textFits ha))
  else none

def unboxConditional :=
  if hi : kid.size < Seal.maxAssociatedDataSize then
    some (PLift.up (fun good : cryptoSeal.Good =>
      unbox_box good rsk esk kid key recipientSize ephemeralSize keyFits hi))
  else none

def UnrestrictedRoundtrip : Prop :=
  ∀ k n ad p, cryptoSeal.dec k n ad (cryptoSeal.enc k n ad p) = some p

def badKeyDisprovesUnrestricted : Option (PLift (¬ UnrestrictedRoundtrip)) :=
  if h : cryptoSeal.dec .empty nonce ad (cryptoSeal.enc .empty nonce ad text) ≠ some text then
    some ⟨fun good => h (good .empty nonce ad text)⟩
  else none

def badNonceDisprovesUnrestricted : Option (PLift (¬ UnrestrictedRoundtrip)) :=
  if h : cryptoSeal.dec key .empty ad (cryptoSeal.enc key .empty ad text) ≠ some text then
    some ⟨fun good => h (good key .empty ad text)⟩
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "concrete supported-domain contract equalities" samplePremises.isSome
  t.ok "Good bridge preserves universal crypto assumption" goodConditional.isSome
  t.ok "sealed body theorem receives all domain premises" openSealedConditional.isSome
  t.ok "member theorem receives all domain premises" memberOpensConditional.isSome
  t.ok "wrapping theorem receives all domain premises" unboxConditional.isSome
  t.ok "former unrestricted empty-key claim still rejected" badKeyDisprovesUnrestricted.isSome
  t.ok "former unrestricted empty-nonce claim still rejected" badNonceDisprovesUnrestricted.isSome
  for size in [0,1,31,33,64] do
    let bad : ByteArray := ⟨Array.replicate size 7⟩
    t.ok s!"key size {size} cannot seal" ((cryptoSeal.enc bad nonce ad text).isEmpty)
    t.ok s!"key size {size} cannot open valid ciphertext"
      (cryptoSeal.dec bad nonce ad (cryptoSeal.enc key nonce ad text) == none)
    t.ok s!"private key size {size} rejects raw DH" ((cryptoSeal.dh bad (cryptoSeal.pub rsk)).isEmpty)
    t.ok s!"public-key output remains 32 bytes for private size {size}" ((cryptoSeal.pub bad).size == 32)
    t.ok s!"malformed private size {size} yields unusable zero public key"
      ((cryptoSeal.dh rsk (cryptoSeal.pub bad)).isEmpty)
  for size in [0,1,23,25,32] do
    let bad : ByteArray := ⟨Array.replicate size 9⟩
    t.ok s!"nonce size {size} cannot seal" ((cryptoSeal.enc key bad ad text).isEmpty)
    t.ok s!"nonce size {size} cannot open valid ciphertext"
      (cryptoSeal.dec key bad ad (cryptoSeal.enc key nonce ad text) == none)
  for fill in [0,7,255] do
    let k : ByteArray := ⟨Array.replicate 32 fill⟩
    let n : ByteArray := ⟨Array.replicate 24 fill⟩
    for p in [ByteArray.empty,text] do
      let encrypted := cryptoSeal.enc k n ad p
      t.ok s!"supported key/nonce {fill}, plaintext {p.size} roundtrips"
        (cryptoSeal.dec k n ad encrypted == some p && encrypted.size == p.size + 16)
    t.ok s!"valid private key {fill} gives shared secret and commutes"
      ((cryptoSeal.dh k (cryptoSeal.pub rsk)).size == 32 &&
       cryptoSeal.dh k (cryptoSeal.pub rsk) == cryptoSeal.dh rsk (cryptoSeal.pub k))
  t.ok "counter bound excludes native rejection point"
    (decide (Seal.maxPlaintextSize - 1 < Seal.maxPlaintextSize) &&
     decide (¬ (Seal.maxPlaintextSize < Seal.maxPlaintextSize)) &&
     decide ((Seal.maxPlaintextSize - 1) / 64 < 2^32 - 1) &&
     decide (¬ (Seal.maxPlaintextSize / 64 < 2^32 - 1)))
  t.ok "associated-data bound excludes unrepresentable length"
    (decide (Seal.maxAssociatedDataSize - 1 < Seal.maxAssociatedDataSize) &&
     decide (¬ (Seal.maxAssociatedDataSize < Seal.maxAssociatedDataSize)))
  t.ok "valid-size sealed body roundtrip"
    (openSealed cryptoSeal room kid (nonce ++ sealBody cryptoSeal key nonce room kid text) key == some text)
  t.ok "valid-size wrapped content key roundtrip"
    (unbox cryptoSeal rsk kid (box cryptoSeal esk (cryptoSeal.pub rsk) kid key) == some key)
  t.ok "wrapped empty payload roundtrips (payload is not the AEAD key)"
    (unbox cryptoSeal rsk kid (box cryptoSeal esk (cryptoSeal.pub rsk) kid .empty) == some .empty)
  t.ok "valid-size wrapped key opens message"
    (((unbox cryptoSeal rsk kid (box cryptoSeal esk (cryptoSeal.pub rsk) kid key)).bind fun k =>
      openSealed cryptoSeal room kid (nonce ++ sealBody cryptoSeal key nonce room kid text) k) == some text)
  t.ok "different associated data rejected"
    (cryptoSeal.dec key nonce "wrong-room".toUTF8 (cryptoSeal.enc key nonce ad text) == none)
  let sealed := cryptoSeal.enc key nonce ad text
  let damaged : ByteArray := ⟨sealed.data.modify 0 fun b => b ^^^ 1⟩
  t.ok "ciphertext corruption rejected" (cryptoSeal.dec key nonce ad damaged == none)
  for size in [0,15,23] do
    t.ok s!"sealed body without complete nonce ({size} bytes) rejected"
      (openSealed cryptoSeal room kid ⟨Array.replicate size 0⟩ key == none)
  for bytes in [ByteArray.empty,ad,room,wrappingKey] do
    t.ok s!"hash supplies 32 bytes for input length {bytes.size}" ((cryptoSeal.hash bytes).size == 32)
  t.finish "seal contract supported inputs and malformed-input regressions"

end Vacuity.SealAudit
