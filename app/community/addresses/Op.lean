import app.community.Op
import engine.wire.Address

/-
A member's dial hints, signed by its admitted device: up to eight IPv4
addresses, detected on its own interfaces (`ds`) or observed by peers
(`os`), with an expiry. The newest a member issued supersedes the rest,
expired or not, so an expiry never brings an older address back.
-/

namespace Community
open Engine Codec

namespace Addresses

/-- What its author writes and signs. -/
structure Body where
  ds : List ByteArray
  os : List ByteArray
  issued : Nat
  expires : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 25 (fun x => (x.ds, x.os, x.issued, x.expires, x.sig))
  (fun (p : List B × List B × Nat × Nat × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) :
    Codec.enc x = 25 :: Codec.enc (x.ds, x.os, x.issued, x.expires, x.sig) := rfl

/-- The body with its signature blanked: what the signature covers. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }

/-- Its fact, `addresses`: whose they are (`peer`, the node key its
admission names) and the hints. -/
structure Fact where
  c : Id
  peer : ByteArray
  ds : List ByteArray
  os : List ByteArray
  issued : Nat
  expires : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 25 (fun x => (x.c, x.peer, x.ds, x.os, x.issued, x.expires))
  (fun (p : B × B × List B × List B × Nat × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
  (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) :
    Codec.enc x = 25 :: Codec.enc (x.c, x.peer, x.ds, x.os, x.issued, x.expires) := rfl

/-- Newest issued first under its key. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.issued

/-! ## The lists its fact is filed in (`addresses.*`) -/
/-- A member node's publications in a community, newest first. -/
def byPeer : Rel Fact := ⟨"addresses", "byPeer", fun f => some [f.c, f.peer]⟩
@[simp] theorem byPeer_args (f : Fact) : byPeer.args f = (some [f.c, f.peer]) := rfl
/-- Every publication: the discovery worker's tailnet seeds. -/
def all : Rel Fact := ⟨"addresses", "all", fun _ => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Addresses

end Community
