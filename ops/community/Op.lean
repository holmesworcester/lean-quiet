import engine.core.Engine
import ops.community.Keys

/-
The community family's root op, and what every op of the family cites:
the signature scheme (`Crypto`, a parameter, so the laws hold for any
scheme), what a signature covers (`signedBy`), and the numbers sort keys
are made of. Every op folder below this one imports it.
-/

namespace Community
open Engine Codec

abbrev Key := ByteArray

structure Crypto where
  verify : Key → ByteArray → ByteArray → Bool
  /-- The public key a 32-byte seed's key pair has. -/
  pub : ByteArray → Key

def decAs {α β} [Codec α] (f : α → β) (bs : List UInt8) : Option (β × List UInt8) :=
  match (dec bs : Option (α × List UInt8)) with
  | none => none
  | some (a, r) => some (f a, r)

theorem decAs_enc {α β} [Codec α] (f : α → β) (a : α) (rest : List UInt8) :
    decAs f (enc a ++ rest) = some (f a, rest) := by
  unfold decAs; rw [Codec.round]

/-- The counter cap: a post claiming this or more is saturated, and is
ordered by this device's receipt of it (`received`). Below 2^64, so a
counter and the cap fit the 8 bytes a sort key gives them. -/
def countCap : Nat := 2 ^ 63

/-- A number as 8 bytes, most significant first, so byte order is
numeric order. -/
def be64 (n : Nat) : ByteArray := ByteArray.mk ((List.range 8).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray

/-- The largest time a sort key tells apart: later claims sort as it. -/
def timeCap : Nat := 2 ^ 64 - 1

/-- The bytes a signature on an op covers: a domain tag, the op's
requirements (its community first) and its unsigned body. -/
def signedBy {β} [Codec β] (o : Op) (b : β) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, o.reqs, b)

/-! ## The root: it founds a community -/

/- The root founds the community; its fact is the founder's admission,
and the founder's user is the community id. The founder is admin. -/
namespace Root

/-- What its author writes and signs. -/
structure Body where
  device : ByteArray
  enc : ByteArray
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 0 (fun x => (x.device, x.enc, x.sig)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 0 :: Codec.enc (x.device, x.enc, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `admission`. -/
structure Fact where
  c : Id
  u : Id
  device : Key
  enc : Key
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 0 (fun x => (x.c, x.u, x.device, x.enc)) (fun (p : B × B × B × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 0 :: Codec.enc (x.c, x.u, x.device, x.enc) := rfl

/-! ## The lists its fact is filed in (`admission.*`) -/
/-- A device's admissions: whom `allowPeer` asks about. -/
def byDevice : Rel Fact := ⟨"admission", "byDevice", fun f => some [f.c, f.device]⟩
@[simp] theorem byDevice_args (f : Fact) : byDevice.args f = (some [f.c, f.device]) := rfl
/-- A community's admissions: whom to dial and seal to. -/
def all : Rel Fact := ⟨"admission", "all", fun f => some [f.c]⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some [f.c]) := rfl
/-- A user's admissions (its devices): whom a removal cites. -/
def byUser : Rel Fact := ⟨"admission", "byUser", fun f => some [f.c, f.u]⟩
@[simp] theorem byUser_args (f : Fact) : byUser.args f = (some [f.c, f.u]) := rfl
/-- The admissions naming an X25519 key: the devices a node's key
speaks for in c, which `allowPeer` asks about. -/
def byKey : Rel Fact := ⟨"admission", "byKey", fun f => some [f.c, f.enc]⟩
@[simp] theorem byKey_args (f : Fact) : byKey.args f = (some [f.c, f.enc]) := rfl

end Root

end Community
