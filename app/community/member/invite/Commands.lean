import app.community.Family

namespace Community
open Engine Codec

/-- An invitation: a request it carries is admitted by one approval. -/
def invite (c issuerAdm : Id) (by_ : Device) (bearer : Key) (link : Bool) : Op :=
  let reqs := [c, issuerAdm]
  mkOp reqs (.invite bearer link (sig by_.sk reqs (.invite bearer link .empty)))

/-- An invitation of c by `by_` (whose admission is `issuerAdm`), on the
node with key `key`, and its link: the bearer key pair from `secret`,
dial hints for the joiner. A device link (`link`) invites another device
of the issuer's user; the link says so, as its invitation does. -/
def issue (c issuerAdm : Id) (by_ : Device) (key : Key) (secret : ByteArray)
    (hints : List ByteArray) (link : Bool := false) : Op × Invite :=
  let inv := invite c issuerAdm by_ (Device.ofSeed secret).pk link
  (inv, ⟨c, inv.id, key, hints, secret, link⟩)
open Engine Codec
namespace Base62

/-- A digit's character: 0-9, A-Z, a-z. -/
def charOf (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else if d < 36 then Char.ofNat (55 + d) else Char.ofNat (61 + d)

def digitOf (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n < 58 then some (n - 48)
  else if 65 ≤ n ∧ n < 91 then some (n - 55)
  else if 97 ≤ n ∧ n < 123 then some (n - 61)
  else none

/-- n's digits, most significant first, ahead of acc. -/
def go (n : Nat) (acc : List Nat) : List Nat :=
  if n < 62 then n :: acc else go (n / 62) (n % 62 :: acc)
termination_by n
decreasing_by omega

def digits (n : Nat) : List Nat := go n []

def ofDigits (m : Nat) (ds : List Nat) : Nat := ds.foldl (fun n d => n * 62 + d) m

/-- Bytes as a number, after a leading 1 so leading zero bytes count. -/
def natOf (l : List UInt8) : Nat := l.foldl (fun n b => n * 256 + b.toNat) 1

/-- A number's base-256 digits below its top digit, and that top digit. -/
def peel (n : Nat) : Nat × List UInt8 :=
  if n < 256 then (n, []) else
    let p := peel (n / 256)
    (p.1, p.2 ++ [(n % 256).toUInt8])
termination_by n
decreasing_by omega

def bytesOf (n : Nat) : Option (List UInt8) :=
  let p := peel n
  if p.1 = 1 then some p.2 else none

/-- Bytes as base62 characters. -/
def encode (l : List UInt8) : List Char := (digits (natOf l)).map charOf

def decode (cs : List Char) : Option (List UInt8) :=
  match cs.mapM digitOf with
  | some ds => bytesOf (ofDigits 0 ds)
  | none => none
end Base62
open Engine Codec

/-- Sizes: 32-byte ids, key and seed; at most 8 hints of at most 255 bytes. -/
def Invite.Valid (i : Invite) : Prop :=
  i.community.size = 32 ∧ i.invitation.size = 32 ∧ i.inviter.size = 32 ∧ i.secret.size = 32 ∧
    i.hints.length ≤ 8 ∧ ∀ h ∈ i.hints, h.size ≤ 255

instance (i : Invite) : Decidable i.Valid := by unfold Invite.Valid; infer_instance

/-- The kind a link's fields lead with: 1 for a member's link, 2 for a
device link (the user's call, 2026-11-01: a device link has a scheme of
its own, as libquiet's `quiet://link/`, and the kind must match it). -/
def kindOf (link : Bool) : Nat := if link then 2 else 1

/-- The fields' bytes, behind their kind. -/
def Invite.bytes (i : Invite) : ByteArray :=
  encode (kindOf i.link, i.community, i.invitation, i.inviter, i.hints, i.secret)

/-- The join page (site/join in this repo). The fields ride after `#`,
which a browser never sends to the server; the page hands them to the
app as a `scheme` URI. -/
def web : List Char := "https://holmesworcester.github.io/lean-quiet/join#".toList

/-- The app's own URI scheme: what the join page opens and the OS hands
the app. -/
def scheme : List Char := "leanquiet://join/".toList

/-- A device link's page (site/link, built from the join page). -/
def webLink : List Char := "https://holmesworcester.github.io/lean-quiet/link#".toList

/-- A device link's URI. -/
def schemeLink : List Char := "leanquiet://link/".toList

/-- The fields in base62. -/
def Invite.code (i : Invite) : List Char := Base62.encode i.bytes.data.toList

/-- The link's text, shared and shown as a QR code: the join page (a
device link's page), with the fields after `#`. -/
def Invite.text (i : Invite) : String := String.ofList ((if i.link then webLink else web) ++ i.code)

/-- The URI the page opens: the scheme and the fields. -/
def Invite.uri (i : Invite) : String := String.ofList ((if i.link then schemeLink else scheme) ++ i.code)

/-- The page or the scheme in front, dropped, and whether it was a device
link's (none: no prefix); any is optional. -/
def unprefix (cs : List Char) : Option Bool × List Char :=
  if web.isPrefixOf cs then (some false, cs.drop web.length)
  else if scheme.isPrefixOf cs then (some false, cs.drop scheme.length)
  else if webLink.isPrefixOf cs then (some true, cs.drop webLink.length)
  else if schemeLink.isPrefixOf cs then (some true, cs.drop schemeLink.length)
  else (none, cs)

/-- An invite from text: whitespace anywhere is ignored (a link broken
across lines still reads); the page or the scheme is optional, but one
of the other kind's refuses it. -/
def Invite.parse (s : String) : Option Invite :=
  let (pre, cs) := unprefix (s.toList.filter fun c => !c.isWhitespace)
  match Base62.decode cs with
  | none => none
  | some bs =>
    match (Codec.decode ⟨bs.toArray⟩ : Option (Nat × Id × Id × Key × List ByteArray × ByteArray)) with
    | some (v, c, inv, k, hs, sec) =>
      let i : Invite := ⟨c, inv, k, hs, sec, v == 2⟩
      if v = kindOf i.link ∧ (pre = none ∨ pre = some i.link) ∧ i.Valid then some i else none
    | none => none

end Community
