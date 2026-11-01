import app.community.Op

/-
An attachment: a child of a message, by the message's author. Its header
is the file's Merkle root and length (`Merkle`); its body,
sealed under the content key, is the name, kind, size, a preview, and the
file's own key. The file is sealed once under that key, and the tree is
over the ciphertext.
-/

namespace Community
open Engine Codec

/-- The largest file an attachment may name: 64 MiB of ciphertext. -/
def maxFile : Nat := 64 * 1024 * 1024

/-- The largest sealed attachment body: an 8 KiB preview, its fields,
and the seal. -/
def maxSealedMeta : Nat := 9 * 1024

namespace Attach

/-- What its author writes and signs. -/
structure Body where
  root : ByteArray
  len : Nat
  kid : ByteArray
  sealed : ByteArray
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 8 (fun x => (x.root, x.len, x.kid, x.sealed, x.sig)) (fun (p : B × Nat × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 8 :: Codec.enc (x.root, x.len, x.kid, x.sealed, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `attachment`. -/
structure Fact where
  c : Id
  msg : Id
  u : Id
  root : Id
  len : Nat
  kid : ByteArray
  sealed : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 7 (fun x => (x.c, x.msg, x.u, x.root, x.len, x.kid, x.sealed)) (fun (p : B × B × B × B × Nat × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 7 :: Codec.enc (x.c, x.msg, x.u, x.root, x.len, x.kid, x.sealed) := rfl

/-! ## The lists its fact is filed in (`attachment.*`) -/
/-- A message's attachments: what its components list. -/
def byMessage : Rel Fact := ⟨"attachment", "byMessage", fun f => some [f.c, f.msg]⟩
@[simp] theorem byMessage_args (f : Fact) : byMessage.args f = (some [f.c, f.msg]) := rfl

end Attach

end Community
