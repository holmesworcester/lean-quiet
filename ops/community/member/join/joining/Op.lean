import ops.community.Op

/-
This device's join in progress: the inviter, the dial hints, the
request it presents, the name chosen. Local.

`community.member.join.joining`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

namespace Joining

/-- What its author writes. -/
structure Body where
  c : Id
  inviter : Key
  hints : List ByteArray
  req : Id
  name : ByteArray
  device : Key
  epoch : Nat
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 14 (fun x => (x.c, x.inviter, x.hints, x.req, x.name, x.device, x.epoch)) (fun (p : B × B × List B × B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 14 :: Codec.enc (x.c, x.inviter, x.hints, x.req, x.name, x.device, x.epoch) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `joining`. -/
structure Fact where
  c : Id
  inviter : Key
  hints : List ByteArray
  req : Id
  name : ByteArray
  device : Key
  epoch : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 13 (fun x => (x.c, x.inviter, x.hints, x.req, x.name, x.device, x.epoch)) (fun (p : B × B × List B × B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 13 :: Codec.enc (x.c, x.inviter, x.hints, x.req, x.name, x.device, x.epoch) := rfl

/-! ## The lists its fact is filed in (`joining.*`) -/
/-- This device's joins: each link and the request it presents. -/
def all : Rel Fact := ⟨"joining", "all", fun f => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Joining

end Community
