import app.community.Op

/-
This device's notification watermark in a community: it has taken
notice of c's posts claiming times up to minute `mark`. A post is news
(it may notify) only above the newest mark, so history that syncs in
after a join, and posts already considered before a restart, never
alert. Local: never sent. Body tag 21, fact tag 19.
-/

namespace Community
open Engine Codec

namespace CaughtUp

/-- What this device writes. -/
structure Body where
  c : Id
  mark : Nat
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 21 (fun x => (x.c, x.mark)) (fun (p : B × Nat) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 21 :: Codec.enc (x.c, x.mark) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b

/-- Its fact, `caughtUp`. -/
structure Fact where
  c : Id
  mark : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 19 (fun x => (x.c, x.mark)) (fun (p : B × Nat) => ⟨p.1, p.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 19 :: Codec.enc (x.c, x.mark) := rfl

/-- Where its fact sorts: by mark, so the newest is first. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.mark

/-! ## The lists its fact is filed in (`caughtUp.*`) -/
def byCommunity : Rel Fact := ⟨"caughtUp", "byCommunity", fun f => some [f.c]⟩
@[simp] theorem byCommunity_args (f : Fact) : byCommunity.args f = (some [f.c]) := rfl

end CaughtUp

end Community
