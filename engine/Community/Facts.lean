/-
A community, after libquiet's DESIGN.md ("A user is its origin op",
"Invite, join, vouch") and its removal stack (#778, #98, #1088):

- The root founds the community; its fact is the founder's admission,
  and the founder's user is the community id. The founder is admin.
- An invite is issued by an admitted device, with a threshold: how
  many members must approve a request it carries, at least one (the
  user's decision, 2026-10-27: approvals are always needed; they are
  where key-material wraps to the new device will hang). A link
  invitation (another device for the issuer's user) needs exactly one
  approval, by the issuer's user, as libquiet's unbound device links
  do. There is no open link: the bearer key alone admits nobody.
- A request redeems an invitation: the requesting device consents
  (signs), and so does the invitation's bearer key from the link. A
  request admits nobody. It is libquiet's Join before its vouches.
- An approval is a member's signed yes to a request, by another device
  than the requester's; a link request is approved by the issuer's user
  only. It cites the request, so approvals come after the request
  without the engine needing forward needs.
- An admission of a request is a tally: it cites the request and
  exactly `threshold` approvals of it, by distinct users. It is
  unsigned (anyone holding the approvals may compose it), and its fact
  is the admission: into a new user named by the request for a member
  invitation, into the issuer's user for a link invitation. Several
  admits of one request (other sets of approvals) all give that same
  admission fact.
- A request is body tag 12; tag 2 (the old join, of the same shape) no
  longer decodes, so an old op is refused rather than misread.
- An admin grants admin to another user. Admin cannot be revoked.
- A removal names a user. It is Valid when its author's user is an
  admin, or removes itself. Validity is read off the cited facts only,
  so every admin-issued removal stands: of other admins, mutually and
  concurrently, and by an admin who has since been removed (confirmed
  by the user, 2026-10-27). In practice such a removal may never spread:
  peers that know of the remover's removal refuse its devices
  (`connect_iff`), so it travels only through peers that do not. When it
  arrives, it is Valid. Removal never invalidates an op; it changes who
  counts as a member.
- A post is a message by an admitted device, under a content key.
- A wrap delivers a content key to one device encryption key; it
  admits nobody, so it needs no author.
- A post's time is its author's claim (it orders a conversation, as
  libquiet's created_at does), and it cites the blobs it attaches.
- A profile is a user's name and avatar, a register: the newest by
  (time, id) is current.
- A blob is an image, named by its bytes' SHA-256: the fact carries the
  hash and size only, and the bytes live outside the engine, stored
  only where their hash matches (as libquiet's chunks). It admits nobody.
- A reaction is an emoji by an admitted device on a message.

Channels and deletion are left out of this first pass.

Signatures are a parameter (`Crypto`), so the laws hold for any scheme;
what unforgeability buys is stated as a hypothesis where it is used.
-/
import Engine

namespace Community
open Engine Codec

abbrev Key := ByteArray

structure Crypto where
  verify : Key → ByteArray → ByteArray → Bool
  /-- The public key a 32-byte seed's key pair has. -/
  pub : ByteArray → Key

inductive Fact where
  | admission (c u : Id) (device enc : Key)
  | invitation (c issuer : Id) (bearer : Key) (link : Bool) (threshold : Nat)
  | admin (c u : Id)
  | removal (c u by_ : Id)
  | message (c u : Id) (device ckey text : ByteArray) (time : Nat) (atts : List Id)
  | wrap (c : Id) (ckey recipient box : ByteArray)
  | profile (c u : Id) (name : ByteArray) (time : Nat) (avatar : List Id)
  | blob (c : Id) (hash : ByteArray) (w h : Nat)
  | react (c u target : Id) (emoji : ByteArray) (time : Nat)
  | request (c u : Id) (device enc : Key) (link : Bool) (threshold : Nat)
  | approval (c req u : Id)
  | secret (pk seed : ByteArray)
  | accepted (c : Id) (device : Key)
  | joining (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray)
  | named (c u : Id) (name : ByteArray) (n : Nat)
  | abandoned (c req : Id)
  deriving DecidableEq, Inhabited

inductive Body where
  | root (device enc sig : ByteArray)
  | invite (bearer : Key) (link : Bool) (threshold : Nat) (sig : ByteArray)
  | request (device enc consent bearerSig : ByteArray)
  | grant (sig : ByteArray)
  | remove (sig : ByteArray)
  | post (ckey text : ByteArray) (time : Nat) (sig : ByteArray)
  | wrap (ckey recipient box : ByteArray)
  | profile (name : ByteArray) (time : Nat) (sig : ByteArray)
  | blob (hash : ByteArray) (w h : Nat)
  | react (emoji : ByteArray) (time : Nat) (sig : ByteArray)
  | approve (sig : ByteArray)
  | admit
  | accept (c : Id) (device : Key)
  | joining (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray)
  | secret (pk seed : ByteArray)
  | name (n : Nat) (name sig : ByteArray)
  | abandon
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
  | .invite k l t s => 1 :: Codec.enc (k, l, t, s)
  | .request d e c b => 12 :: Codec.enc (d, e, c, b)
  | .grant s => 3 :: Codec.enc s
  | .remove s => 4 :: Codec.enc s
  | .post k t tm s => 5 :: Codec.enc (k, t, tm, s)
  | .wrap k r b => 6 :: Codec.enc (k, r, b)
  | .profile n tm s => 7 :: Codec.enc (n, tm, s)
  | .blob hh w h => 8 :: Codec.enc (hh, w, h)
  | .react e tm s => 9 :: Codec.enc (e, tm, s)
  | .approve s => 10 :: Codec.enc s
  | .admit => [11]
  | .accept c d => 13 :: Codec.enc (c, d)
  | .joining c k hs r nm => 14 :: Codec.enc (c, k, hs, r, nm)
  | .secret pk seed => 15 :: Codec.enc (pk, seed)
  | .name n nm s => 16 :: Codec.enc (n, nm, s)
  | .abandon => [17]

def Body.dec : List UInt8 → Option (Body × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B) => Body.root p.1 p.2.1 p.2.2) r
  | 1 :: r => decAs (fun (p : B × Bool × Nat × B) => Body.invite p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 3 :: r => decAs (fun (p : B) => Body.grant p) r
  | 4 :: r => decAs (fun (p : B) => Body.remove p) r
  | 5 :: r => decAs (fun (p : B × B × Nat × B) => Body.post p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 6 :: r => decAs (fun (p : B × B × B) => Body.wrap p.1 p.2.1 p.2.2) r
  | 7 :: r => decAs (fun (p : B × Nat × B) => Body.profile p.1 p.2.1 p.2.2) r
  | 8 :: r => decAs (fun (p : B × Nat × Nat) => Body.blob p.1 p.2.1 p.2.2) r
  | 9 :: r => decAs (fun (p : B × Nat × B) => Body.react p.1 p.2.1 p.2.2) r
  | 10 :: r => decAs (fun (p : B) => Body.approve p) r
  | 11 :: r => some (.admit, r)
  | 12 :: r => decAs (fun (p : B × B × B × B) => Body.request p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 13 :: r => decAs (fun (p : B × B) => Body.accept p.1 p.2) r
  | 14 :: r => decAs (fun (p : B × B × List B × B × B) =>
      Body.joining p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 15 :: r => decAs (fun (p : B × B) => Body.secret p.1 p.2) r
  | 16 :: r => decAs (fun (p : Nat × B × B) => Body.name p.1 p.2.1 p.2.2) r
  | 17 :: r => some (.abandon, r)
  | _ => none

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round b rest := by
    cases b <;> simp only [Body.enc, Body.dec, List.cons_append] <;>
      first | rfl | exact decAs_enc _ _ _

def Fact.enc : Fact → List UInt8
  | .admission c u d e => 0 :: Codec.enc (c, u, d, e)
  | .invitation c i k l t => 1 :: Codec.enc (c, i, k, l, t)
  | .admin c u => 2 :: Codec.enc (c, u)
  | .removal c u b => 3 :: Codec.enc (c, u, b)
  | .message c u d k t tm a => 4 :: Codec.enc (c, u, d, k, t, tm, a)
  | .wrap c k r b => 5 :: Codec.enc (c, k, r, b)
  | .profile c u n tm a => 6 :: Codec.enc (c, u, n, tm, a)
  | .blob c hh w h => 7 :: Codec.enc (c, hh, w, h)
  | .react c u t e tm => 8 :: Codec.enc (c, u, t, e, tm)
  | .request c u d e l t => 9 :: Codec.enc (c, u, d, e, l, t)
  | .approval c r u => 10 :: Codec.enc (c, r, u)
  | .secret pk seed => 11 :: Codec.enc (pk, seed)
  | .accepted c d => 12 :: Codec.enc (c, d)
  | .joining c k hs r nm => 13 :: Codec.enc (c, k, hs, r, nm)
  | .named c u nm n => 14 :: Codec.enc (c, u, nm, n)
  | .abandoned c r => 15 :: Codec.enc (c, r)

def Fact.dec : List UInt8 → Option (Fact × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B × B) => Fact.admission p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 1 :: r => decAs (fun (p : B × B × B × Bool × Nat) =>
      Fact.invitation p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 2 :: r => decAs (fun (p : B × B) => Fact.admin p.1 p.2) r
  | 3 :: r => decAs (fun (p : B × B × B) => Fact.removal p.1 p.2.1 p.2.2) r
  | 4 :: r => decAs (fun (p : B × B × B × B × B × Nat × List B) =>
      Fact.message p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) r
  | 5 :: r => decAs (fun (p : B × B × B × B) => Fact.wrap p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 6 :: r => decAs (fun (p : B × B × B × Nat × List B) =>
      Fact.profile p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 7 :: r => decAs (fun (p : B × B × Nat × Nat) => Fact.blob p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 8 :: r => decAs (fun (p : B × B × B × B × Nat) => Fact.react p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 9 :: r => decAs (fun (p : B × B × B × B × Bool × Nat) =>
      Fact.request p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) r
  | 10 :: r => decAs (fun (p : B × B × B) => Fact.approval p.1 p.2.1 p.2.2) r
  | 11 :: r => decAs (fun (p : B × B) => Fact.secret p.1 p.2) r
  | 12 :: r => decAs (fun (p : B × B) => Fact.accepted p.1 p.2) r
  | 13 :: r => decAs (fun (p : B × B × List B × B × B) =>
      Fact.joining p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 14 :: r => decAs (fun (p : B × B × B × Nat) => Fact.named p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 15 :: r => decAs (fun (p : B × B) => Fact.abandoned p.1 p.2) r
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
  | .invite k l t _ => .invite k l t .empty
  | .request d e _ _ => .request d e .empty .empty
  | .grant _ => .grant .empty
  | .remove _ => .remove .empty
  | .post k t tm _ => .post k t tm .empty
  | .profile n tm _ => .profile n tm .empty
  | .react e tm _ => .react e tm .empty
  | .approve _ => .approve .empty
  | .name n nm _ => .name n nm .empty
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

/-- Whether every fact is a blob of community c. -/
def blobsOf (c : Id) : List Fact → Bool
  | [] => true
  | .blob c' .. :: rest => decide (c' = c) && blobsOf c rest
  | _ :: _ => false

/-- The users of these facts, if every one approves request r of c. -/
def approvers (c r : Id) : List Fact → Option (List Id)
  | [] => some []
  | .approval c' r' u :: rest =>
    if c' = c ∧ r' = r then (approvers c r rest).map (u :: ·) else none
  | _ :: _ => none

/-- The highest counter of these names of c (0 for none), if every fact
is one. -/
def prevMax (c : Id) : List Fact → Option Nat
  | [] => some 0
  | .named c' _ _ k :: rest => if c' = c then (prevMax c rest).map (max k) else none
  | _ :: _ => none

/-- Whether n is one more than the highest counter of the names cited. -/
def counterOk (c : Id) (n : Nat) (fs : List Fact) : Bool :=
  match prevMax c fs with
  | some m => decide (n = m + 1)
  | none => false

/-- Whether these facts are exactly t approvals of request r of c, by
t distinct users. -/
def tally (c r : Id) (t : Nat) (fs : List Fact) : Bool :=
  match approvers c r fs with
  | some us => decide (us.Nodup ∧ us.length = t)
  | none => false

/-- An op's validator, by its body, over the facts its requirements
produced (slot order). Slot 0 is the community's root, whose fact is
the founder's admission with the community's id. -/
def check (C : Crypto) (o : Op) : Body → List Fact → Option Fact
  | .root d e s, [] =>
    if C.verify d (signed o (.root d e s)) s then some (.admission o.id o.id d e) else none
  | .invite k l t s, [.admission c u0 _ _, .admission c' u d _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ 1 ≤ t ∧ (l = true → t = 1) ∧
      C.verify d (signed o (.invite k l t s)) s
    then some (.invitation c u k l t) else none
  | .request d e cs bs, [.admission c u0 _ _, .invitation c' issuer k l t] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ C.verify d (signed o (.request d e cs bs)) cs ∧
      C.verify k (signed o (.request d e cs bs)) bs
    then some (.request c (if l then issuer else o.id) d e l t) else none
  -- The pattern forces exactly three requirements, so slot 1 is the
  -- request the approval names.
  | .approve s, [.admission c u0 _ _, .request c1 u d _ l _, .admission c2 a da _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ (l = true → a = u) ∧ da ≠ d ∧
      C.verify da (signed o (.approve s)) s
    then some (.approval c (o.reqs.getD 1 .empty) a) else none
  | .admit, .admission c u0 _ _ :: .request c1 u d e _ t :: aps =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ tally c (o.reqs.getD 1 .empty) t aps = true
    then some (.admission c u d e) else none
  | .grant s, [.admission c u0 _ _, .admission c1 u d _, auth, .admission c2 t _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ isAdmin c u auth ∧
      C.verify d (signed o (.grant s)) s
    then some (.admin c t) else none
  | .remove s, [.admission c u0 _ _, .admission c1 u d _, auth, .admission c2 t _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ (t = u ∨ isAdmin c u auth) ∧
      C.verify d (signed o (.remove s)) s
    then some (.removal c t u) else none
  | .post k txt tm s, .admission c u0 _ _ :: .admission c1 u d _ :: rest =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ blobsOf c rest = true ∧
      C.verify d (signed o (.post k txt tm s)) s
    then some (.message c u d k txt tm (o.reqs.drop 2)) else none
  | .profile n tm s, .admission c u0 _ _ :: .admission c1 u d _ :: rest =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ rest.length ≤ 1 ∧ blobsOf c rest = true ∧
      n.size ≤ 64 ∧ C.verify d (signed o (.profile n tm s)) s
    then some (.profile c u n tm (o.reqs.drop 2)) else none
  | .blob hh w h, [.admission c u0 _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ hh.size = 32 ∧ 0 < w ∧ w ≤ 4096 ∧ 0 < h ∧ h ≤ 4096
    then some (.blob c hh w h) else none
  | .react e tm s, [.admission c u0 _ _, .admission c1 u d _, .message c2 _ _ _ _ _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ 0 < e.size ∧ e.size ≤ 32 ∧
      C.verify d (signed o (.react e tm s)) s
    then some (.react c u (o.reqs.getD 2 .empty) e tm) else none
  | .wrap k r bx, [.admission c u0 _ _] =>
    if o.reqs.head? = some c ∧ u0 = c then some (.wrap c k r bx) else none
  | .secret pk seed, [] => if C.pub seed = pk then some (.secret pk seed) else none
  | .accept c d, [] => some (.accepted c d)
  | .joining c k hs r nm, [] => some (.joining c k hs r nm)
  | .abandon, [.joining c _ _ r _] => some (.abandoned c r)
  | .name n nm s, .admission c u0 _ _ :: .admission c1 u d _ :: auth :: prev =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ isAdmin c u auth ∧ nm.size ≤ 64 ∧
      counterOk c n prev = true ∧ C.verify d (signed o (.name n nm s)) s
    then some (.named c u nm n) else none
  | _, _ => none

def validate (C : Crypto) (o : Op) (fs : List Fact) : Option Fact :=
  match (decode o.body : Option Body) with
  | none => none
  | some b => check C o b fs

/-! ## Relations: the lists facts are filed in, by name -/

namespace admission
/-- A device's admissions: whom `allowPeer` asks about. -/
def byDevice : Rel Fact := ⟨"admission", "byDevice", fun | .admission c _ d _ => some [c, d] | _ => none⟩
/-- A community's admissions: whom to dial and seal to. -/
def all : Rel Fact := ⟨"admission", "all", fun | .admission c .. => some [c] | _ => none⟩
end admission

namespace removal
def byUser : Rel Fact := ⟨"removal", "byUser", fun | .removal c u _ => some [c, u] | _ => none⟩
end removal

namespace admin
def byUser : Rel Fact := ⟨"admin", "byUser", fun | .admin c u => some [c, u] | _ => none⟩
end admin

namespace message
def all : Rel Fact := ⟨"message", "all", fun | .message c .. => some [c] | _ => none⟩
def byAuthor : Rel Fact := ⟨"message", "byAuthor", fun | .message c u .. => some [c, u] | _ => none⟩
end message

namespace wrap
def byContentKey : Rel Fact := ⟨"wrap", "byContentKey", fun | .wrap c k _ _ => some [c, k] | _ => none⟩
end wrap

namespace profile
def byUser : Rel Fact := ⟨"profile", "byUser", fun | .profile c u .. => some [c, u] | _ => none⟩
def all : Rel Fact := ⟨"profile", "all", fun | .profile c .. => some [c] | _ => none⟩
end profile

namespace react
def byMessage : Rel Fact := ⟨"react", "byMessage", fun | .react c _ t _ _ => some [c, t] | _ => none⟩
def byMessageEmoji : Rel Fact :=
  ⟨"react", "byMessageEmoji", fun | .react c _ t e _ => some [c, t, e] | _ => none⟩
end react

namespace request
/-- A community's pending requests: what approvers are asked about. Never
the admission relations: a request grants no connection and no content
key. -/
def all : Rel Fact := ⟨"request", "all", fun | .request c .. => some [c] | _ => none⟩
end request

namespace approval
def byRequest : Rel Fact := ⟨"approval", "byRequest", fun | .approval c r _ => some [c, r] | _ => none⟩
end approval

namespace secret
/-- This device's own secret seeds, by public key: read by intents to
sign, never by views. -/
def byKey : Rel Fact := ⟨"secret", "byKey", fun | .secret pk _ => some [pk] | _ => none⟩
/-- Every device this node holds the secret of: the devices its network
node speaks for. -/
def all : Rel Fact := ⟨"secret", "all", fun | .secret .. => some [] | _ => none⟩
end secret

namespace accepted
/-- The communities this device is in, joined or waiting. -/
def all : Rel Fact := ⟨"accepted", "all", fun | .accepted .. => some [] | _ => none⟩
end accepted

namespace joining
/-- This device's joins: each link and the request it presents. -/
def all : Rel Fact := ⟨"joining", "all", fun | .joining .. => some [] | _ => none⟩
end joining

namespace abandoned
/-- The joins this device stopped waiting on, by request. -/
def byRequest : Rel Fact := ⟨"abandoned", "byRequest", fun | .abandoned _ r => some [r] | _ => none⟩
end abandoned

namespace named
/-- A community's names, by counter: the current one is the list read
newest first, limit 1. -/
def current : Rel Fact := ⟨"named", "current", fun | .named c .. => some [c] | _ => none⟩
end named

/-- Every relation of the community's facts. Invitations and blobs are
in none (read by their own key). -/
def rels : List (Rel Fact) :=
  [admission.byDevice, admission.all, removal.byUser, admin.byUser, message.all, message.byAuthor,
   wrap.byContentKey, profile.byUser, profile.all, react.byMessage, react.byMessageEmoji,
   request.all, approval.byRequest, secret.byKey, secret.all, accepted.all, joining.all, named.current,
   abandoned.byRequest]

/-- The keys a fact is filed under: its relations'. -/
def keys : Fact → List ByteArray := keysOf rels

/-- A number as 8 bytes, most significant first, so byte order is
numeric order. -/
def be64 (n : Nat) : ByteArray := ByteArray.mk ((List.range 8).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray

/-- Where a fact sorts under its keys: timed facts by time (ties by id). -/
def sortOf : Fact → ByteArray
  | .message _ _ _ _ _ tm _ => be64 tm
  | .profile _ _ _ tm _ => be64 tm
  | .react _ _ _ _ tm => be64 tm
  | .named _ _ _ n => be64 n
  | _ => .empty

instance : SortKey Fact := ⟨sortOf⟩

/-- Whether an op is local, from its body: a device's secrets, its
acceptances and its joins are, never sent or taken; everything else is
shared in its community. -/
def Body.isLocal : Body → Bool
  | .secret .. | .accept .. | .joining .. | .abandon => true
  | _ => false

/-- The community an op is about: a root founds its own; every other op
names its community first. -/
def Body.community (b : Body) (o : Op) : Id :=
  match b with
  | .root .. => o.id
  | _ => o.reqs.headD o.id

/-- Where an op travels: local, or shared in its community. -/
def scopeOf (o : Op) : Scope :=
  match (decode o.body : Option Body) with
  | some b => if b.isLocal then .local else .shared (b.community o)
  | none => .shared (o.reqs.headD o.id)

/-- An op's claimed time, which sync ranges are over: a post's, a
profile's or a reaction's; 0 for the rest (roots, invitations,
admissions, removals, ...), which every window includes. -/
def orderOf (o : Op) : Nat :=
  match (decode o.body : Option Body) with
  | some (.post _ _ t _) | some (.profile _ t _) | some (.react _ t _) => t
  | _ => 0

def family (C : Crypto) : Family Fact :=
  { validate := validate C, keys, scope := scopeOf, order := orderOf }

end Community
