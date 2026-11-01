import app.community.Op

/-
Stop waiting on a join. Local.
-/

namespace Community
open Engine Codec

namespace Abandon

/-- What its author writes. -/
structure Body where
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 17 (fun _ => ()) (fun _ => {}) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = [17] := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `abandoned`. -/
structure Fact where
  c : Id
  req : Id
  join : Id
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 15 (fun x => (x.c, x.req, x.join)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 15 :: Codec.enc (x.c, x.req, x.join) := rfl

/-! ## The lists its fact is filed in (`abandoned.*`) -/
/-- The joins this device stopped waiting on, by request. -/
def byRequest : Rel Fact := ⟨"abandoned", "byRequest", fun f => some [f.req]⟩
@[simp] theorem byRequest_args (f : Fact) : byRequest.args f = (some [f.req]) := rfl
def byJoining : Rel Fact := ⟨"abandoned", "byJoining", fun f => some [f.join]⟩
@[simp] theorem byJoining_args (f : Fact) : byJoining.args f = (some [f.join]) := rfl

end Abandon

end Community
