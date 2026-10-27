/-
A community, after libquiet's DESIGN.md ("A user is its origin op",
"Invite, join, vouch") and its removal stack (#778, #98, #1088):

- The root founds the community; its fact is the founder's admission,
  and the founder's user is the community id. The founder is admin.
- An invite is issued by an admitted device. A join redeems it: the
  joining device consents (signs), and so does the invitation's bearer
  key from the link. A member invitation starts a new user, named by
  the join; a link invitation adds a device to the issuer's user.
- An admin grants admin to another user. Admin cannot be revoked.
- A removal names a user. It is Valid when its author's user is an
  admin, or removes itself. Validity is read off the cited facts only,
  so every admin-issued removal stands: of other admins, mutually and
  concurrently, and by an admin who has since been removed. Removal
  never invalidates an op; it changes who counts as a member.
- A post is a message by an admitted device, under a content key.
- A wrap delivers a content key to one device encryption key; it
  admits nobody, so it needs no author.

Vouching, channels and deletion are left out of this first pass.

Signatures are a parameter (`Crypto`), so the laws hold for any scheme;
what unforgeability buys is stated as a hypothesis where it is used.
-/
import Engine

namespace Community
open Engine Codec

abbrev Key := ByteArray

structure Crypto where
  verify : Key → ByteArray → ByteArray → Bool

inductive Fact where
  | admission (c u : Id) (device enc : Key)
  | invitation (c issuer : Id) (bearer : Key) (link : Bool)
  | admin (c u : Id)
  | removal (c u by_ : Id)
  | message (c u : Id) (device ckey text : ByteArray)
  | wrap (c : Id) (ckey recipient box : ByteArray)
  deriving DecidableEq, Inhabited

inductive Body where
  | root (device enc sig : ByteArray)
  | invite (bearer : Key) (link : Bool) (sig : ByteArray)
  | join (device enc consent bearerSig : ByteArray)
  | grant (sig : ByteArray)
  | remove (sig : ByteArray)
  | post (ckey text sig : ByteArray)
  | wrap (ckey recipient box : ByteArray)
  deriving DecidableEq, Inhabited

/-! ## Bytes -/

def decAs {α β} [Codec α] (f : α → β) (bs : List UInt8) : Option (β × List UInt8) :=
  match (dec bs : Option (α × List UInt8)) with
  | none => none
  | some (a, r) => some (f a, r)

theorem decAs_enc {α β} [Codec α] (f : α → β) (a : α) (rest : List UInt8) :
    decAs f (enc a ++ rest) = some (f a, rest) := by
  unfold decAs; rw [Codec.round]

abbrev B := ByteArray

def Body.enc : Body → List UInt8
  | .root d e s => 0 :: Codec.enc (d, e, s)
  | .invite k l s => 1 :: Codec.enc (k, l, s)
  | .join d e c b => 2 :: Codec.enc (d, e, c, b)
  | .grant s => 3 :: Codec.enc s
  | .remove s => 4 :: Codec.enc s
  | .post k t s => 5 :: Codec.enc (k, t, s)
  | .wrap k r b => 6 :: Codec.enc (k, r, b)

def Body.dec : List UInt8 → Option (Body × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B) => Body.root p.1 p.2.1 p.2.2) r
  | 1 :: r => decAs (fun (p : B × Bool × B) => Body.invite p.1 p.2.1 p.2.2) r
  | 2 :: r => decAs (fun (p : B × B × B × B) => Body.join p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 3 :: r => decAs (fun (p : B) => Body.grant p) r
  | 4 :: r => decAs (fun (p : B) => Body.remove p) r
  | 5 :: r => decAs (fun (p : B × B × B) => Body.post p.1 p.2.1 p.2.2) r
  | 6 :: r => decAs (fun (p : B × B × B) => Body.wrap p.1 p.2.1 p.2.2) r
  | _ => none

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round b rest := by
    cases b <;> simp only [Body.enc, Body.dec, List.cons_append] <;> exact decAs_enc _ _ _

def Fact.enc : Fact → List UInt8
  | .admission c u d e => 0 :: Codec.enc (c, u, d, e)
  | .invitation c i k l => 1 :: Codec.enc (c, i, k, l)
  | .admin c u => 2 :: Codec.enc (c, u)
  | .removal c u b => 3 :: Codec.enc (c, u, b)
  | .message c u d k t => 4 :: Codec.enc (c, u, d, k, t)
  | .wrap c k r b => 5 :: Codec.enc (c, k, r, b)

def Fact.dec : List UInt8 → Option (Fact × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B × B) => Fact.admission p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 1 :: r => decAs (fun (p : B × B × B × Bool) => Fact.invitation p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 2 :: r => decAs (fun (p : B × B) => Fact.admin p.1 p.2) r
  | 3 :: r => decAs (fun (p : B × B × B) => Fact.removal p.1 p.2.1 p.2.2) r
  | 4 :: r => decAs (fun (p : B × B × B × B × B) => Fact.message p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 5 :: r => decAs (fun (p : B × B × B × B) => Fact.wrap p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | _ => none

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round f rest := by
    cases f <;> simp only [Fact.enc, Fact.dec, List.cons_append] <;> exact decAs_enc _ _ _

/-! ## Signing -/

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned : Body → Body
  | .root d e _ => .root d e .empty
  | .invite k l _ => .invite k l .empty
  | .join d e _ _ => .join d e .empty .empty
  | .grant _ => .grant .empty
  | .remove _ => .remove .empty
  | .post k t _ => .post k t .empty
  | b => b

/-- The bytes a signature on an op covers: a domain tag, the op's
requirements (its community first) and its unsigned body. -/
def signed (o : Op) (b : Body) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, o.reqs, b.unsigned)

/-! ## Validity -/

/-- Whether a fact shows that user u of community c is admin: the
founder's admission (the founder's user is the community), or a grant. -/
def isAdmin (c u : Id) : Fact → Bool
  | .admission c' u' _ _ => decide (c' = c ∧ u' = c ∧ u = c)
  | .admin c' u' => decide (c' = c ∧ u' = u)
  | _ => false

/-- An op's validator, by its body, over the facts its requirements
produced (slot order). Slot 0 is the community's root, whose fact is
the founder's admission with the community's id. -/
def check (C : Crypto) (o : Op) : Body → List Fact → Option Fact
  | .root d e s, [] =>
    if C.verify d (signed o (.root d e s)) s then some (.admission o.id o.id d e) else none
  | .invite k l s, [.admission c u0 _ _, .admission c' u d _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ C.verify d (signed o (.invite k l s)) s
    then some (.invitation c u k l) else none
  | .join d e cs bs, [.admission c u0 _ _, .invitation c' issuer k l] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ C.verify d (signed o (.join d e cs bs)) cs ∧
      C.verify k (signed o (.join d e cs bs)) bs
    then some (.admission c (if l then issuer else o.id) d e) else none
  | .grant s, [.admission c u0 _ _, .admission c1 u d _, auth, .admission c2 t _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ isAdmin c u auth ∧
      C.verify d (signed o (.grant s)) s
    then some (.admin c t) else none
  | .remove s, [.admission c u0 _ _, .admission c1 u d _, auth, .admission c2 t _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ (t = u ∨ isAdmin c u auth) ∧
      C.verify d (signed o (.remove s)) s
    then some (.removal c t u) else none
  | .post k txt s, [.admission c u0 _ _, .admission c1 u d _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ C.verify d (signed o (.post k txt s)) s
    then some (.message c u d k txt) else none
  | .wrap k r bx, [.admission c u0 _ _] =>
    if o.reqs.head? = some c ∧ u0 = c then some (.wrap c k r bx) else none
  | _, _ => none

def validate (C : Crypto) (o : Op) (fs : List Fact) : Option Fact :=
  match (decode o.body : Option Body) with
  | none => none
  | some b => check C o b fs

/-! ## Index keys -/

def key (t : Nat) (c x : ByteArray) : ByteArray := encode (t, c, x)

/-- Admissions by device (0) and all of a community's (1), removals by
user (2), grants by user (3), messages (4), wraps by content key (5). -/
def keys : Fact → List ByteArray
  | .admission c _ d _ => [key 0 c d, key 1 c c]
  | .invitation .. => []
  | .admin c u => [key 3 c u]
  | .removal c u _ => [key 2 c u]
  | .message c .. => [key 4 c c]
  | .wrap c k _ _ => [key 5 c k]

def family (C : Crypto) : Family Fact := ⟨validate C, keys⟩

end Community
