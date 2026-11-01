import tests.engine.Lib

/-! The sealing laws, applied to the running suite (`cryptoSeal`) and the
functions the app runs. Keys and nonces are sized (`Key32`, `Nonce24`), so
no size premise is left to discharge: the fixtures' sizes are proved by
`rfl` when they are built. What is left is the crypto trust file's
assumption (`Trust.Native`): each theorem's instance takes it as its one
premise (the *conditional* bridges below), and the executable checks the
instance's conclusion directly on the native crates. Wrong sizes cannot be
passed at all; the controls show the stored-key path refuses them, and that
the native crates refute the old unsized roundtrip. -/
namespace Vacuity.SealAudit
open Engine Community Tests
set_option linter.defProp false

def key : Key32 := ⟨⟨Array.replicate 32 7⟩, rfl⟩
def nonce : Nonce24 := ⟨⟨Array.replicate 24 9⟩, rfl⟩
def room : ByteArray := ⟨Array.replicate 32 11⟩
def text := "Hello Bob, this is an encrypted test message.".toUTF8
def ad := "quiet-vacuity-associated-data".toUTF8
def rsk : Key32 := ⟨⟨Array.replicate 32 13⟩, rfl⟩
def esk : Key32 := ⟨⟨Array.replicate 32 17⟩, rfl⟩
def kid := kidOf cryptoSeal key
def admission : Id := ⟨Array.replicate 32 19⟩
def poster := Device.named "vacuity seal poster"

theorem roomSize : room.size = 32 := by decide +kernel
theorem textFits : text.size < Crypto.maxPlaintext := by decide +kernel

/-- The plaintext bound is the stream cipher's remaining-block check,
including its ceiling for a partial block. No 256 GiB buffer is needed. -/
theorem counterBound (n : Nat) : n < Crypto.maxPlaintext ↔ (n + 63) / 64 ≤ 2^32 - 2 := by
  unfold Crypto.maxPlaintext
  omega

/-! ## Conditional bridges: the instances, given the trust file -/

def goodConditional := some (PLift.up (fun t : Trust.Native => cryptoSeal_good t))

def openSealedConditional :=
  if ha : (bodyAd room kid).size < Crypto.maxAD then
    some (PLift.up (fun t : Trust.Native =>
      openSealed_seal (c := room) (kid := kid) (text := text) (cryptoSeal_good t) key nonce textFits ha))
  else none

def memberOpensConditional :=
  if ha : (bodyAd room kid).size < Crypto.maxAD then
    some (PLift.up (fun t : Trust.Native =>
      member_opens (cryptoSeal_good t) rsk esk key nonce room text textFits ha))
  else none

def unboxConditional :=
  if hi : kid.size < Crypto.maxAD then
    some (PLift.up (fun t : Trust.Native => unbox_box (cryptoSeal_good t) rsk esk key kid hi))
  else none

/-- The app's own path: the poster's `sealedPost`, read back by the
screen's `openStored` (`sealedPost_opens`). -/
def postOpensConditional := some (PLift.up (fun t : Trust.Native =>
  sealedPost_opens t room admission poster key nonce text 1 29880000 none roomSize textFits))

/-- The approver's `wrapKey`, opened by the member's `unbox`
(`wrapKey_opens`). -/
def wrapOpensConditional := some (PLift.up (fun t : Trust.Native => wrapKey_opens t room key esk rsk))

/-- All four together (`member_reads`). -/
def memberReadsConditional := some (PLift.up (fun t : Trust.Native =>
  member_reads t room admission poster key esk rsk nonce text 1 29880000 none roomSize textFits))

/-! ## The old unsized roundtrip, refuted by the native crates -/

def UnsizedRoundtrip : Prop :=
  ∀ k n ad p, Crypto.xchachaOpen k n ad (Crypto.xchachaSeal k n ad p) = some p

def badKeyRefutesUnsized : Option (PLift (¬ UnsizedRoundtrip)) :=
  if h : Crypto.xchachaOpen .empty nonce.1 ad (Crypto.xchachaSeal .empty nonce.1 ad text) ≠ some text then
    some ⟨fun good => h (good .empty nonce.1 ad text)⟩
  else none

def badNonceRefutesUnsized : Option (PLift (¬ UnsizedRoundtrip)) :=
  if h : Crypto.xchachaOpen key.1 .empty ad (Crypto.xchachaSeal key.1 .empty ad text) ≠ some text then
    some ⟨fun good => h (good key.1 .empty ad text)⟩
  else none

/-- The post the app writes, decoded: its key id and sealed bytes. -/
def posted : Option (ByteArray × ByteArray) :=
  match (Codec.decode (sealedPost room admission poster key nonce text 1 29880000).body : Option Body) with
  | some (.post k s _ _ _) => some (k, s)
  | _ => none

/-- The wrap the app writes to rsk's node key, decoded. -/
def wrapped : Option (ByteArray × ByteArray) :=
  match (Codec.decode (wrapKey room key esk (cryptoSeal.pub rsk)).body : Option Body) with
  | some (.wrap k _ b) => some (k, b)
  | _ => none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "trust-file bridge to the running suite" goodConditional.isSome
  t.ok "sealed body theorem receives every premise" openSealedConditional.isSome
  t.ok "member theorem receives every premise" memberOpensConditional.isSome
  t.ok "wrapping theorem receives every premise" unboxConditional.isSome
  t.ok "post-path instance receives every premise" postOpensConditional.isSome
  t.ok "wrap-path instance receives every premise" wrapOpensConditional.isSome
  t.ok "member-read instance receives every premise" memberReadsConditional.isSome
  t.ok "the native refutes the unsized roundtrip at an empty key" badKeyRefutesUnsized.isSome
  t.ok "the native refutes the unsized roundtrip at an empty nonce" badNonceRefutesUnsized.isSome
  -- The instances' conclusions, on the native crates and the app's own ops.
  match posted with
  | some (k, s) =>
    t.ok "the post's key id is the key's" (k == kid)
    t.ok "the screen's read path opens the app's post to its text"
      (openStored cryptoSeal room k s key.1 == some text)
    t.ok "a different 32-byte key opens nothing" (openStored cryptoSeal room k s rsk.1 == none)
    t.ok "another community's id opens nothing" (openStored cryptoSeal admission k s key.1 == none)
    for size in [0, 1, 31, 33, 64] do
      t.ok s!"a stored key of {size} bytes is refused before the native call"
        (openStored cryptoSeal room k s ⟨Array.replicate size 7⟩ == none &&
          (Bytes.of? (n := 32) ⟨Array.replicate size 7⟩).isNone)
    let damaged : ByteArray := ⟨s.data.modify 30 fun b => b ^^^ 1⟩
    t.ok "a same-size tampered body fails the tag" (openStored cryptoSeal room k damaged key.1 == none)
    for size in [0, 15, 23] do
      t.ok s!"a body without its whole nonce ({size} bytes) is refused"
        (openStored cryptoSeal room k ⟨Array.replicate size 0⟩ key.1 == none)
  | none => t.ok "the app's post decodes" false
  match wrapped with
  | some (k, b) =>
    t.ok "the member unboxes the app's wrap to the content key" (unbox cryptoSeal rsk k b == some key)
    t.ok "another node's secret unboxes nothing" (unbox cryptoSeal esk k b == none)
    t.ok "the unboxed key opens the post"
      ((posted.bind fun (pk, s) => (unbox cryptoSeal rsk k b).bind fun k' =>
        openStored cryptoSeal room pk s k'.1) == some text)
  | none => t.ok "the app's wrap decodes" false
  -- The AEAD itself, across plaintext lengths that cross ChaCha20's 64-byte
  -- blocks, and the hash and key sizes the laws use.
  for fill in [0, 7, 255] do
    let k : Key32 := Bytes.fit 32 ⟨Array.replicate 32 fill⟩
    let n : Nonce24 := Bytes.fit 24 ⟨Array.replicate 24 fill⟩
    for len in [0, 1, 63, 64, 65, 1000] do
      let p : ByteArray := ⟨Array.replicate len 42⟩
      let c := cryptoSeal.enc k n ad p
      t.ok s!"key/nonce {fill}, plaintext {len}: opens back, 16 bytes longer"
        (cryptoSeal.dec k n ad c == some p && c.size == len + 16)
    t.ok s!"secret {fill} agrees with rsk"
      (cryptoSeal.dh k (cryptoSeal.pub rsk) == cryptoSeal.dh rsk (cryptoSeal.pub k) &&
        (cryptoSeal.pub k).size == 32)
  t.ok "different associated data is refused"
    (cryptoSeal.dec key nonce "wrong-room".toUTF8 (cryptoSeal.enc key nonce ad text) == none)
  for bytes in [ByteArray.empty, ad, room] do
    t.ok s!"hash supplies 32 bytes for input length {bytes.size}" ((cryptoSeal.hash bytes).size == 32)
  t.ok "plaintext bound matches the native remaining-block check"
    (Crypto.maxPlaintext == 274877906817 &&
     decide ((Crypto.maxPlaintext - 1 + 63) / 64 ≤ 2^32 - 2) &&
     decide (¬ ((Crypto.maxPlaintext + 63) / 64 ≤ 2^32 - 2)))
  t.finish "sealing laws at the running suite and the app's ops"

end Vacuity.SealAudit
