import app.community.Op

/-
A content key delivered to a node's X25519 key, sealed so that only that
node opens it. A wrap admits nobody, so it needs no author.
-/

namespace Community
open Engine Codec

namespace Wrap

/-- What its author writes. -/
structure Body where
  ckey : ByteArray
  recipient : ByteArray
  box : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 6 (fun x => (x.ckey, x.recipient, x.box)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 6 :: Codec.enc (x.ckey, x.recipient, x.box) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `wrap`. -/
structure Fact where
  c : Id
  ckey : ByteArray
  recipient : ByteArray
  box : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 5 (fun x => (x.c, x.ckey, x.recipient, x.box)) (fun (p : B × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 5 :: Codec.enc (x.c, x.ckey, x.recipient, x.box) := rfl

/-! ## The lists its fact is filed in (`wrap.*`) -/
def byContentKey : Rel Fact := ⟨"wrap", "byContentKey", fun f => some [f.c, f.ckey]⟩
@[simp] theorem byContentKey_args (f : Fact) : byContentKey.args f = (some [f.c, f.ckey]) := rfl
/-- The keys wrapped to a device's X25519 key in c. -/
def byRecipient : Rel Fact := ⟨"wrap", "byRecipient", fun f => some [f.c, f.recipient]⟩
@[simp] theorem byRecipient_args (f : Fact) : byRecipient.args f = (some [f.c, f.recipient]) := rfl

end Wrap

end Community
