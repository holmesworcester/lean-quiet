import app.community.Op

/-
Where the dialer's scan of pending joins and members stands: the last
position it visited in each list, and the node keys it visited (whose
older retry clocks and observations `stale` then names). Local. The
newest supersedes the rest.
-/

namespace Community
open Engine Codec

namespace Scan

/-- What the dialer writes. -/
structure Body where
  cursor : ByteArray
  visited : List ByteArray
  time : Nat
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 29 (fun x => (x.cursor, x.visited, x.time))
  (fun (p : B × List B × Nat) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 29 :: Codec.enc (x.cursor, x.visited, x.time) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b

/-- Its fact, `scan`. -/
structure Fact where
  cursor : ByteArray
  visited : List ByteArray
  time : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 29 (fun x => (x.cursor, x.visited, x.time))
  (fun (p : B × List B × Nat) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 29 :: Codec.enc (x.cursor, x.visited, x.time) := rfl

/-- Newest first. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`scan.*`) -/
/-- The scan's positions, newest first. -/
def all : Rel Fact := ⟨"scan", "all", fun _ => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Scan

end Community
