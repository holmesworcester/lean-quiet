import app.community.Op
import engine.wire.Address

/-
A member's report of where it saw another member's node: the remote IP
of an authenticated session, with that node's listening port. Signed by
the reporter's admitted device. A hint for the target to republish in
its own `addresses`, never a certificate of reachability.
-/

namespace Community
open Engine Codec

namespace Sighting

/-- What its author writes and signs. -/
structure Body where
  target : ByteArray
  addr : ByteArray
  time : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 26 (fun x => (x.target, x.addr, x.time, x.sig))
  (fun (p : B × B × Nat × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) :
    Codec.enc x = 26 :: Codec.enc (x.target, x.addr, x.time, x.sig) := rfl

/-- The body with its signature blanked: what the signature covers. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }

/-- Its fact, `sighting`. -/
structure Fact where
  c : Id
  reporter : ByteArray
  target : ByteArray
  addr : ByteArray
  time : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 26 (fun x => (x.c, x.reporter, x.target, x.addr, x.time))
  (fun (p : B × B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) :
    Codec.enc x = 26 :: Codec.enc (x.c, x.reporter, x.target, x.addr, x.time) := rfl

/-- Newest first under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`sighting.*`) -/
/-- Where members saw a node, newest first: what it republishes. -/
def byTarget : Rel Fact := ⟨"sighting", "byTarget", fun f => some [f.c, f.target]⟩
@[simp] theorem byTarget_args (f : Fact) : byTarget.args f = (some [f.c, f.target]) := rfl
/-- One reporter's sightings of one node: its own rate limit. -/
def byReporter : Rel Fact := ⟨"sighting", "byReporter", fun f => some [f.c, f.reporter, f.target]⟩
@[simp] theorem byReporter_args (f : Fact) : byReporter.args f = (some [f.c, f.reporter, f.target]) := rfl

end Sighting

end Community
