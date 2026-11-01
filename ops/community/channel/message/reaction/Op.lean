import ops.community.Op

/-
An emoji on a message, by an admitted device.

`community.channel.message.reaction`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace React

/-- What its author writes and signs. -/
structure Body where
  emoji : ByteArray
  time : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 9 (fun x => (x.emoji, x.time, x.sig)) (fun (p : B × Nat × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 9 :: Codec.enc (x.emoji, x.time, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }



/-- Its fact, `react`. -/
structure Fact where
  c : Id
  u : Id
  target : Id
  emoji : ByteArray
  time : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 8 (fun x => (x.c, x.u, x.target, x.emoji, x.time)) (fun (p : B × B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 8 :: Codec.enc (x.c, x.u, x.target, x.emoji, x.time) := rfl

/-- Where its fact sorts under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`react.*`) -/
def byMessage : Rel Fact := ⟨"react", "byMessage", fun f => some [f.c, f.target]⟩
@[simp] theorem byMessage_args (f : Fact) : byMessage.args f = (some [f.c, f.target]) := rfl
def byMessageEmoji : Rel Fact := ⟨"react", "byMessageEmoji", fun f => some [f.c, f.target, f.emoji]⟩
@[simp] theorem byMessageEmoji_args (f : Fact) : byMessageEmoji.args f = (some [f.c, f.target, f.emoji]) := rfl

end React

end Community
