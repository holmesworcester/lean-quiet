import app.community.Op

/-
A removal names a user. It is Valid when its author's user is an admin,
or removes itself. Removal never invalidates an op; it changes who counts
as a member (docs/REMOVAL.md). After its four requirements it cites the
head of each removed device's approval chain its author holds: its cut.
-/

namespace Community
open Engine Codec

namespace Remove

/-- What its author writes and signs. -/
structure Body where
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 4 (fun x => x.sig) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 4 :: Codec.enc x.sig := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `removal`: the community, the user removed, its author's
user, and its cut: for each approval chain head it cites, the device
whose chain it is, the head's id, and the head's place in the chain.
The removed user's approvals at or behind a head it cites keep counting;
its devices' other approvals admit no one (`Kept`, docs/REMOVAL.md). -/
structure Fact where
  c : Id
  u : Id
  by_ : Id
  cut : List (Key × Id × Nat)
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 3 (fun x => (x.c, x.u, x.by_, x.cut))
  (fun (p : B × B × B × List (B × B × Nat)) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 3 :: Codec.enc (x.c, x.u, x.by_, x.cut) := rfl

/-! ## The lists its fact is filed in (`removal.*`) -/
def byUser : Rel Fact := ⟨"removal", "byUser", fun f => some [f.c, f.u]⟩
@[simp] theorem byUser_args (f : Fact) : byUser.args f = (some [f.c, f.u]) := rfl

end Remove

end Community
