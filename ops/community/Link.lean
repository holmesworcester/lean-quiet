/-
The invite link: what an inviter shows (as text or a QR code) and a
joiner pastes or scans. After libquiet's invite link: a scheme, then the
fields in base62.

It carries the community (its root's id), the invitation op's id, the
inviter's device key (whom to dial, and the one device the joiner trusts
before any ops arrive: Net.Node's link clause), dial hints ("ip:port",
possibly none: mDNS finds the inviter), and the 32-byte bearer seed the
invitation's bearer key pair derives from. No community name: the
joiner learns it from the ops it syncs.

Laws: `parse_text` (the text of a valid invite parses back to it) and
`parse_valid` (whatever parses is valid: ids, keys and the seed have
their sizes, at most 8 hints of at most 255 bytes). `parse` reads only
through `decode` and checked list operations, so any text is safe to
paste.
-/
import ops.community.Compose

namespace Community
open Engine Codec

/-! ## Base62 -/

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

theorem digitOf_charOf : ∀ d, d < 62 → digitOf (charOf d) = some d := by decide

theorem charOf_not_ws : ∀ d, d < 62 → (charOf d).isWhitespace = false := by decide

/-- n's digits, most significant first, ahead of acc. -/
def go (n : Nat) (acc : List Nat) : List Nat :=
  if n < 62 then n :: acc else go (n / 62) (n % 62 :: acc)
termination_by n
decreasing_by omega

def digits (n : Nat) : List Nat := go n []

def ofDigits (m : Nat) (ds : List Nat) : Nat := ds.foldl (fun n d => n * 62 + d) m

theorem ofDigits_go (n : Nat) (acc : List Nat) : ofDigits 0 (go n acc) = ofDigits n acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rw [go]
    split
    · simp [ofDigits]
    · rename_i h
      rw [ih (n / 62) (by omega)]
      simp only [ofDigits, List.foldl_cons]
      rw [Nat.div_add_mod' n 62]

theorem go_lt (n : Nat) (acc : List Nat) (h : ∀ d ∈ acc, d < 62) : ∀ d ∈ go n acc, d < 62 := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rw [go]
    split
    · rename_i hn; intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hn
      · exact h d hd
    · exact ih (n / 62) (by omega) _ fun d hd => by
        rcases List.mem_cons.1 hd with rfl | hd
        · exact Nat.mod_lt _ (by decide)
        · exact h d hd

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

/-- Peeling a number with bytes appended gives those bytes back. -/
theorem peel_foldl (l : List UInt8) (m : Nat) (hm : 1 ≤ m) :
    peel (l.foldl (fun n b => n * 256 + b.toNat) m) = ((peel m).1, (peel m).2 ++ l) := by
  induction l generalizing m with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih _ (by omega)]
    have hb := b.toNat_lt
    have e : peel (m * 256 + b.toNat) = ((peel m).1, (peel m).2 ++ [b]) := by
      rw [peel, if_neg (by omega)]
      have h1 : (m * 256 + b.toNat) / 256 = m := by omega
      have h2 : (m * 256 + b.toNat) % 256 = b.toNat := by omega
      have hb' : b.toNat.toUInt8 = b := UInt8.ofNat_toNat
      simp only [h1, h2, hb']
    rw [e]; simp

theorem peel_natOf (l : List UInt8) : peel (natOf l) = (1, l) := by
  unfold natOf
  rw [peel_foldl l 1 (by decide)]
  simp [peel]

theorem bytesOf_natOf (l : List UInt8) : bytesOf (natOf l) = some l := by
  unfold bytesOf; rw [peel_natOf]; rfl

/-- Bytes as base62 characters. -/
def encode (l : List UInt8) : List Char := (digits (natOf l)).map charOf

def decode (cs : List Char) : Option (List UInt8) :=
  match cs.mapM digitOf with
  | some ds => bytesOf (ofDigits 0 ds)
  | none => none

theorem mapM_digitOf (ds : List Nat) (h : ∀ d ∈ ds, d < 62) : (ds.map charOf).mapM digitOf = some ds := by
  induction ds with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, List.mapM_cons, digitOf_charOf d (h d (List.mem_cons_self ..)),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem decode_encode (l : List UInt8) : decode (encode l) = some l := by
  have hlt : ∀ d ∈ digits (natOf l), d < 62 := go_lt _ _ (by simp)
  have hd : ofDigits 0 (digits (natOf l)) = natOf l := ofDigits_go _ _
  unfold decode encode
  rw [mapM_digitOf _ hlt]
  show bytesOf (ofDigits 0 (digits (natOf l))) = some l
  rw [hd, bytesOf_natOf]

theorem encode_not_ws (l : List UInt8) : ∀ c ∈ encode l, c.isWhitespace = false := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact charOf_not_ws d (go_lt _ _ (by simp) d hd)

end Base62

/-! ## The link -/

structure Invite where
  community : Id
  invitation : Id
  inviter : Key
  hints : List ByteArray
  secret : ByteArray
  deriving DecidableEq, Inhabited

/-- Sizes: 32-byte ids, key and seed; at most 8 hints of at most 255 bytes. -/
def Invite.Valid (i : Invite) : Prop :=
  i.community.size = 32 ∧ i.invitation.size = 32 ∧ i.inviter.size = 32 ∧ i.secret.size = 32 ∧
    i.hints.length ≤ 8 ∧ ∀ h ∈ i.hints, h.size ≤ 255

instance (i : Invite) : Decidable i.Valid := by unfold Invite.Valid; infer_instance

def linkVersion : Nat := 1

/-- The fields' bytes, behind a version. -/
def Invite.bytes (i : Invite) : ByteArray :=
  encode (linkVersion, i.community, i.invitation, i.inviter, i.hints, i.secret)

def scheme : List Char := "quiet://join/".toList

/-- The link's text: the scheme and the fields in base62. -/
def Invite.text (i : Invite) : String := String.ofList (scheme ++ Base62.encode i.bytes.data.toList)

/-- An invite from text: whitespace anywhere is ignored (a link broken
across lines still reads), the scheme is optional. -/
def Invite.parse (s : String) : Option Invite :=
  let cs := s.toList.filter fun c => !c.isWhitespace
  let cs := if scheme.isPrefixOf cs then cs.drop scheme.length else cs
  match Base62.decode cs with
  | none => none
  | some bs =>
    match (Codec.decode ⟨bs.toArray⟩ : Option (Nat × Id × Id × Key × List ByteArray × ByteArray)) with
    | some (v, c, inv, k, hs, sec) =>
      let i : Invite := ⟨c, inv, k, hs, sec⟩
      if v = linkVersion ∧ i.Valid then some i else none
    | none => none

theorem scheme_not_ws : ∀ c ∈ scheme, c.isWhitespace = false := by decide

theorem isPrefixOf_self_append (l x : List Char) : l.isPrefixOf (l ++ x) = true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.isPrefixOf, ih]

/-- **A valid invite's text parses back to it.** -/
theorem parse_text {i : Invite} (hv : i.Valid) : Invite.parse i.text = some i := by
  unfold Invite.parse Invite.text
  rw [String.toList_ofList]
  have hf : (scheme ++ Base62.encode i.bytes.data.toList).filter (fun c => !c.isWhitespace) =
      scheme ++ Base62.encode i.bytes.data.toList := by
    refine List.filter_eq_self.2 fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · simp [scheme_not_ws c hc]
    · simp [Base62.encode_not_ws _ c hc]
  simp only [hf, isPrefixOf_self_append, ite_true, List.drop_left, Base62.decode_encode]
  rw [show (⟨i.bytes.data.toList.toArray⟩ : ByteArray) = i.bytes from rfl, Invite.bytes,
    Codec.decode_encode]
  simp only
  rw [if_pos (by first | exact ⟨rfl, hv⟩ | exact ⟨trivial, hv⟩ | exact hv)]

/-- **Whatever parses is valid.** -/
theorem parse_valid {s : String} {i : Invite} (h : Invite.parse s = some i) : i.Valid := by
  unfold Invite.parse at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hv; cases h; exact hv.2
      · cases h
    · cases h

/-! ## Composing from a link -/

/-- The invitation's bearer key pair, from the link's seed. -/
def Invite.bearer (i : Invite) : Device := Device.ofSeed i.secret

/-- The joiner's request, composed from the link: device d asks to join
through the link's invitation, signed by d and by the bearer key. -/
def Invite.request (i : Invite) (d : Device) : Op :=
  Community.request i.community i.invitation d i.bearer.sk

/-- An invitation of c by `by_` (whose admission is `issuerAdm`), and its
link: the bearer key pair from `secret`, dial hints for the joiner. -/
def issue (c issuerAdm : Id) (by_ : Device) (secret : ByteArray) (hints : List ByteArray)
    (threshold : Nat := 1) : Op × Invite :=
  let inv := invite c issuerAdm by_ (Device.ofSeed secret).pk false threshold
  (inv, ⟨c, inv.id, by_.pk, hints, secret⟩)

/-- This device's pending join (local): the link's community, its
inviter and hints, the request the join presents, and the name to
introduce itself by once admitted. The bearer seed is not kept: the
request already carries the bearer's signature. -/
def joining (i : Invite) (req : Id) (name : ByteArray) (device : Key) (epoch : Nat := 0) : Op :=
  mkOp [] (.joining i.community i.inviter i.hints req name device epoch)

/-- This device stops waiting on a join (local): its joining op is cited,
the request stays with the members, and an approval still admits it. -/
def abandon (joiningOp : Id) : Op := mkOp [joiningOp] .abandon

end Community
