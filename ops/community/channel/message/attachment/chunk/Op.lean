import ops.community.Op

/-
One 64 KiB slice of a file's ciphertext with its Merkle path. It cites
its community and its attachment, and is Valid iff it names its
attachment's root and length and its path verifies against them.

`community.channel.message.attachment.chunk`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Chunk

/-- What its author writes. -/
structure Body where
  root : ByteArray
  len : Nat
  index : Nat
  slice : ByteArray
  sibs : List ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 19 (fun x => (x.root, x.len, x.index, x.slice, x.sibs)) (fun (p : B × Nat × Nat × B × List B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 19 :: Codec.enc (x.root, x.len, x.index, x.slice, x.sibs) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `chunk`. -/
structure Fact where
  c : Id
  att : Id
  root : Id
  len : Nat
  index : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 17 (fun x => (x.c, x.att, x.root, x.len, x.index)) (fun (p : B × B × B × Nat × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 17 :: Codec.enc (x.c, x.att, x.root, x.len, x.index) := rfl

/-- Where its fact sorts under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.index

/-! ## The lists its fact is filed in (`chunk.*`) -/
/-- An attachment's chunks, by index: their count is the download's
progress (`Community.progress`); read in order, they assemble the file. -/
def byAttachment : Rel Fact := ⟨"chunk", "byAttachment", fun f => some [f.c, f.att]⟩
@[simp] theorem byAttachment_args (f : Fact) : byAttachment.args f = (some [f.c, f.att]) := rfl

end Chunk

end Community
