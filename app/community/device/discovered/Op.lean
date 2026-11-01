import app.community.Op
import engine.wire.Address

/-
What this node's DNS-SD browser heard a known node announce: its key, up
to eight IPv4 hints, when, and for how long. Local: a dial hint, never
sent. The newest per node supersedes the rest.
-/

namespace Community
open Engine Codec

namespace Discovered

/-- What the discovery worker writes. -/
structure Body where
  peer : ByteArray
  hints : List ByteArray
  time : Nat
  ttl : Nat
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 27 (fun x => (x.peer, x.hints, x.time, x.ttl))
  (fun (p : B × List B × Nat × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) :
    Codec.enc x = 27 :: Codec.enc (x.peer, x.hints, x.time, x.ttl) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b

/-- Its fact, `discovered`. -/
structure Fact where
  peer : ByteArray
  hints : List ByteArray
  time : Nat
  ttl : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 27 (fun x => (x.peer, x.hints, x.time, x.ttl))
  (fun (p : B × List B × Nat × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) :
    Codec.enc x = 27 :: Codec.enc (x.peer, x.hints, x.time, x.ttl) := rfl

/-- Newest first under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`discovered.*`) -/
/-- What was heard from a node, newest first. -/
def byPeer : Rel Fact := ⟨"discovered", "byPeer", fun f => some [f.peer]⟩
@[simp] theorem byPeer_args (f : Fact) : byPeer.args f = (some [f.peer]) := rfl
/-- Every observation, newest first: what `stale` scans. -/
def all : Rel Fact := ⟨"discovered", "all", fun _ => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Discovered

end Community
