import app.community.Op

/-
A request redeems an invitation: the requesting device consents (signs),
and so does the invitation's bearer key from the link. It admits nobody.
Body tag 12; tag 2, the old join, no longer decodes.
-/

namespace Community
open Engine Codec

namespace Request

/-- What its author writes and signs. -/
structure Body where
  device : ByteArray
  enc : ByteArray
  consent : ByteArray
  bearerSig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 12 (fun x => (x.device, x.enc, x.consent, x.bearerSig)) (fun (p : B × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 12 :: Codec.enc (x.device, x.enc, x.consent, x.bearerSig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with consent := .empty, bearerSig := .empty }


/-- Its fact, `request`. -/
structure Fact where
  c : Id
  u : Id
  device : Key
  enc : Key
  link : Bool
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 9 (fun x => (x.c, x.u, x.device, x.enc, x.link)) (fun (p : B × B × B × B × Bool) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 9 :: Codec.enc (x.c, x.u, x.device, x.enc, x.link) := rfl

/-! ## The lists its fact is filed in (`request.*`) -/
/-- A community's pending requests: what approvers are asked about. Never
the admission relations: a request grants no connection and no content
key. -/
def all : Rel Fact := ⟨"request", "all", fun f => some [f.c]⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some [f.c]) := rfl

end Request

end Community
