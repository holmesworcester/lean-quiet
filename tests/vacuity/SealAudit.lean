import tests.engine.Lib

/-! The production suite rejects wrong-sized keys and nonces. Seal.Good asks
for roundtrips for *all* byte arrays, so its universal premise is false of the
actual suite. Successful runtime branches below construct its negation using
the very field a caller would need. No crypto axiom/native_decide is added.
Valid-sized fixtures are exercised separately and do not discharge Good. -/
namespace Vacuity.SealAudit
open Engine Community Tests

def key : ByteArray := ⟨Array.replicate 32 7⟩
def nonce : ByteArray := ⟨Array.replicate 24 9⟩
def room : ByteArray := ⟨Array.replicate 32 11⟩
def text := "Hello Bob, this is an encrypted test message.".toUTF8
def ad := "quiet-vacuity-associated-data".toUTF8
def rsk : ByteArray := ⟨Array.replicate 32 13⟩
def esk : ByteArray := ⟨Array.replicate 32 17⟩
def kid := kidOf cryptoSeal key

def badKeyDisprovesGood : Option (PLift (¬ cryptoSeal.Good)) :=
  if h : cryptoSeal.dec .empty nonce ad (cryptoSeal.enc .empty nonce ad text) ≠ some text then
    some ⟨fun good => h (good.dec_enc .empty nonce ad text)⟩
  else none

def badNonceDisprovesGood : Option (PLift (¬ cryptoSeal.Good)) :=
  if h : cryptoSeal.dec key .empty ad (cryptoSeal.enc key .empty ad text) ≠ some text then
    some ⟨fun good => h (good.dec_enc key .empty ad text)⟩
  else none

-- Record the actual theorem applications without pretending the global premise
-- was established. All data arguments and the nonce-size proof are concrete.
def openSealedConditional (good : cryptoSeal.Good) :=
  openSealed_seal (c := room) (kid := kid) (k := key) (n := nonce) (text := text)
    good (by decide +kernel)
def memberOpensConditional (good : cryptoSeal.Good) :=
  member_opens good rsk esk key nonce room text (by decide +kernel)
def unboxConditional (good : cryptoSeal.Good) := unbox_box good rsk esk kid key

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "empty key disproves actual Seal.Good.dec_enc" badKeyDisprovesGood.isSome
  t.ok "empty nonce disproves actual Seal.Good.dec_enc" badNonceDisprovesGood.isSome
  t.ok "wrong-sized key seals to empty" ((cryptoSeal.enc .empty nonce ad text).isEmpty)
  t.ok "wrong-sized key opens to none" (cryptoSeal.dec .empty nonce ad (cryptoSeal.enc .empty nonce ad text) == none)
  t.ok "valid-size AEAD roundtrip" (cryptoSeal.dec key nonce ad (cryptoSeal.enc key nonce ad text) == some text)
  t.ok "valid-size sealed body roundtrip"
    (openSealed cryptoSeal room kid (nonce ++ sealBody cryptoSeal key nonce room kid text) key == some text)
  t.ok "valid-size wrapped content key roundtrip"
    (unbox cryptoSeal rsk kid (box cryptoSeal esk (cryptoSeal.pub rsk) kid key) == some key)
  t.ok "valid-size wrapped key opens message"
    (((unbox cryptoSeal rsk kid (box cryptoSeal esk (cryptoSeal.pub rsk) kid key)).bind fun k =>
      openSealed cryptoSeal room kid (nonce ++ sealBody cryptoSeal key nonce room kid text) k) == some text)
  t.ok "different associated data rejected"
    (cryptoSeal.dec key nonce "wrong-room".toUTF8 (cryptoSeal.enc key nonce ad text) == none)
  t.finish "seal assumption audit (2 concrete counterexamples to Good)"

end Vacuity.SealAudit
