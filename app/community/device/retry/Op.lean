import app.community.Op

/-
This node's last dial attempt to a node: when, and how many in a row.
Local. Per node, not per address, so a new advertisement cannot reset
the backoff. The newest per node supersedes the rest.
-/

namespace Community
open Engine Codec

namespace Retry

/-- What the dialer writes. -/
structure Body where
  peer : ByteArray
  time : Nat
  attempts : Nat
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 28 (fun x => (x.peer, x.time, x.attempts))
  (fun (p : B × Nat × Nat) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 28 :: Codec.enc (x.peer, x.time, x.attempts) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b

/-- Its fact, `retry`. -/
structure Fact where
  peer : ByteArray
  time : Nat
  attempts : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 28 (fun x => (x.peer, x.time, x.attempts))
  (fun (p : B × Nat × Nat) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 28 :: Codec.enc (x.peer, x.time, x.attempts) := rfl

/-- Newest first under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`retry.*`) -/
/-- A node's attempts, newest first. -/
def byPeer : Rel Fact := ⟨"retry", "byPeer", fun f => some [f.peer]⟩
@[simp] theorem byPeer_args (f : Fact) : byPeer.args f = (some [f.peer]) := rfl
/-- Every attempt, newest first: what `stale` scans. -/
def all : Rel Fact := ⟨"retry", "all", fun _ => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Retry

end Community
