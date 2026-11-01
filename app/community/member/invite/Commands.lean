import app.community.Family

/-!
`community.member.invite`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- An invitation needing `threshold` approvals (one by default; a link
invitation needs exactly one). -/
def invite (c issuerAdm : Id) (by_ : Device) (bearer : Key) (link : Bool)
    (threshold : Nat := 1) : Op :=
  let reqs := [c, issuerAdm]
  mkOp reqs (.invite bearer link threshold (sig by_.sk reqs (.invite bearer link threshold .empty)))

/-- An invitation of c by `by_` (whose admission is `issuerAdm`), on the
node with key `key`, and its link: the bearer key pair from `secret`,
dial hints for the joiner. -/
def issue (c issuerAdm : Id) (by_ : Device) (key : Key) (secret : ByteArray)
    (hints : List ByteArray) (threshold : Nat := 1) : Op × Invite :=
  let inv := invite c issuerAdm by_ (Device.ofSeed secret).pk false threshold
  (inv, ⟨c, inv.id, key, hints, secret⟩)
end Community
namespace Community
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
end Community
namespace Community
open Engine Codec

/-- Sizes: 32-byte ids, key and seed; at most 8 hints of at most 255 bytes. -/
def Invite.Valid (i : Invite) : Prop :=
  i.community.size = 32 ∧ i.invitation.size = 32 ∧ i.inviter.size = 32 ∧ i.secret.size = 32 ∧
    i.hints.length ≤ 8 ∧ ∀ h ∈ i.hints, h.size ≤ 255

instance (i : Invite) : Decidable i.Valid := by unfold Invite.Valid; infer_instance

def linkVersion : Nat := 1

/-- The fields' bytes, behind a version. -/
def Invite.bytes (i : Invite) : ByteArray :=
  encode (linkVersion, i.community, i.invitation, i.inviter, i.hints, i.secret)

/-- The join page (site/join in this repo). The fields ride after `#`,
which a browser never sends to the server; the page hands them to the
app as a `scheme` URI. -/
def web : List Char := "https://holmesworcester.github.io/lean-quiet/join#".toList

/-- The app's own URI scheme: what the join page opens and the OS hands
the app. -/
def scheme : List Char := "leanquiet://join/".toList

/-- The fields in base62. -/
def Invite.code (i : Invite) : List Char := Base62.encode i.bytes.data.toList

/-- The link's text, shared and shown as a QR code: the join page, with
the fields after `#`. -/
def Invite.text (i : Invite) : String := String.ofList (web ++ i.code)

/-- The URI the join page opens: the scheme and the fields. -/
def Invite.uri (i : Invite) : String := String.ofList (scheme ++ i.code)

/-- The join page or the scheme in front, dropped; either is optional. -/
def unprefix (cs : List Char) : List Char :=
  if web.isPrefixOf cs then cs.drop web.length
  else if scheme.isPrefixOf cs then cs.drop scheme.length else cs

/-- An invite from text: whitespace anywhere is ignored (a link broken
across lines still reads); the join page or the scheme is optional. -/
def Invite.parse (s : String) : Option Invite :=
  let cs := unprefix (s.toList.filter fun c => !c.isWhitespace)
  match Base62.decode cs with
  | none => none
  | some bs =>
    match (Codec.decode ⟨bs.toArray⟩ : Option (Nat × Id × Id × Key × List ByteArray × ByteArray)) with
    | some (v, c, inv, k, hs, sec) =>
      let i : Invite := ⟨c, inv, k, hs, sec⟩
      if v = linkVersion ∧ i.Valid then some i else none
    | none => none

end Community
