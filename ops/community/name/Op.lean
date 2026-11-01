import ops.community.Op

/-
The community's name, set by an admin. Counted: a new name's counter is
one more than the highest it cites, so the newest wins.

`community.name`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Rename

/-- What its author writes and signs. -/
structure Body where
  n : Nat
  name : ByteArray
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 16 (fun x => (x.n, x.name, x.sig)) (fun (p : Nat × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 16 :: Codec.enc (x.n, x.name, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `named`. -/
structure Fact where
  c : Id
  u : Id
  name : ByteArray
  n : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 14 (fun x => (x.c, x.u, x.name, x.n)) (fun (p : B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 14 :: Codec.enc (x.c, x.u, x.name, x.n) := rfl

/-- Where its fact sorts under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.n

/-! ## The lists its fact is filed in (`named.*`) -/
/-- A community's names, by counter: the current one is the list read
newest first, limit 1. -/
def current : Rel Fact := ⟨"named", "current", fun f => some [f.c]⟩
@[simp] theorem current_args (f : Fact) : current.args f = (some [f.c]) := rfl

end Rename

end Community
