/-
A community, after libquiet's DESIGN.md ("A user is its origin op",
"Invite, join, vouch") and its removal stack (#778, #98, #1088):

- The root founds the community; its fact is the founder's admission,
  and the founder's user is the community id. The founder is admin.
- An invite is issued by an admitted device, with a threshold: how
  many members must approve a request it carries, at least one (the
  user's decision, 2026-10-27: approvals are always needed). A link
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
- A post is a message by an admitted device. Its body is sealed: it
  names a content key by id and carries the nonce and ciphertext
  (`Community.Keys`). Its header is clear: the key id, the time, the
  signature, which covers the sealed bytes. Validators read only the
  header, so a keyless node judges a post as a member does.
- A content key is local (`key`): this device's copy of a community's
  key. A wrap delivers one to an X25519 key, sealed so that only that
  key's holder opens it. A wrap serves one admission: it cites it, and
  is Valid only if its recipient is that admission's encryption key
  (`wrap_cites_admission`). So a wrap is Valid only where its admission
  is (`wrap_only_admitted`). The founder wraps the first key to itself,
  citing the root; after that `shareKey` wraps a device's key to every
  live admission (`recipients`) whose key holds none, citing it
  (`shareKey_recipients`, `shareKey_complete`): the devices of the
  users who approved it at once, any other holder only once the new
  member's profile is a grace old with no wrap held, so an admission's
  wraps of a key are at most its approvers' devices plus those fallback
  holders (`wraps_bounded`). An approval writes no wrap
  (`approveReq_ops`), so nothing reaches a requester before its
  admission. A wrap admits nobody, so it needs no author.
- A post claims two numbers: a counter, which orders its channel, and
  a time, wall-clock minutes since the Unix epoch, which is shown (the
  user's decision, 2026-10-28: "don't hack order onto time"). A
  channel's list sorts by (counter, time, id), and a new post's counter
  is one more than the highest its author holds (`send`), so it sorts
  after everything its author had seen. Both are claims: validating the
  counter would mean citing earlier messages, pulling a channel's whole
  history into every closure. So one post claiming the cap or more
  (`countCap`) saturates the channel: every later post claims the cap.
  Past the cap a device orders by its own receipts instead (`received`,
  a local op written when a saturated post arrives or is sent): the one
  place two devices may order alike messages differently (the user's
  decision, 2026-10-27, stated as `order_local`).
- A post is body tag 23 and its message fact tag 21; tags 5 and 4 (the
  post and message before the counter) no longer decode.
- A profile is a user's name, a register: the newest by (time, id) is
  current.
- An attachment is a child of a message, by the message's author, as
  libquiet's op graph has it: a message has any number of children, and
  components list them (`attachment.byMessage`). Its header is the
  file's Merkle root and length (`Community.Merkle`); its body, sealed
  under the content key, is the name, kind, size, a preview, and the
  file's own key. The file is sealed once under that key, and the tree is
  over the ciphertext.
- A chunk is one 64 KiB slice of a file's ciphertext with its Merkle
  path. It cites its community and its attachment (never another
  chunk, so chunks fetch in parallel), and it is Valid iff it names its
  attachment's root and length and its path verifies against them. So
  it authenticates itself, any peer may relay it, and each is one
  attachment's: the same file sent twice is two sets of chunks, and a
  message's dependents reach all of its chunks. An attachment's chunks
  are listed by `chunk.byAttachment [c, att]`; a count of them over the
  chunk count is the download's progress.
- A reaction is an emoji by an admitted device on a message.

Channels and deletion are left out of this first pass.

Signatures are a parameter (`Crypto`), so the laws hold for any scheme;
what unforgeability buys is stated as a hypothesis where it is used.
-/
import engine.core.Engine
import ops.community.Keys
import ops.community.Merkle
import engine.renderer.Chars

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
  | message (c u : Id) (device ckey text : ByteArray) (n time : Nat)
  | wrap (c : Id) (ckey recipient box : ByteArray)
  | profile (c u : Id) (name : ByteArray) (time : Nat)
  | attachment (c msg u root : Id) (len : Nat) (kid sealed : ByteArray)
  | react (c u target : Id) (emoji : ByteArray) (time : Nat)
  | request (c u : Id) (device enc : Key) (link : Bool) (threshold : Nat)
  | approval (c req u : Id)
  | secret (pk seed : ByteArray)
  | accepted (c : Id) (device : Key)
  | joining (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray)
      (device : Key) (epoch : Nat)
  | named (c u : Id) (name : ByteArray) (n : Nat)
  | abandoned (c req join : Id)
  | key (c kid k : ByteArray)
  | chunk (c att root : Id) (len index : Nat)
  | received (c kid msg : Id) (k : Nat)
  deriving DecidableEq, Inhabited

inductive Body where
  | root (device enc sig : ByteArray)
  | invite (bearer : Key) (link : Bool) (threshold : Nat) (sig : ByteArray)
  | request (device enc consent bearerSig : ByteArray)
  | grant (sig : ByteArray)
  | remove (sig : ByteArray)
  | post (ckey text : ByteArray) (n time : Nat) (sig : ByteArray)
  | wrap (ckey recipient box : ByteArray)
  | profile (name : ByteArray) (time : Nat) (sig : ByteArray)
  | attach (root : ByteArray) (len : Nat) (kid sealed sig : ByteArray)
  | react (emoji : ByteArray) (time : Nat) (sig : ByteArray)
  | approve (sig : ByteArray)
  | admit
  | accept (c : Id) (device : Key)
  | joining (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray)
      (device : Key) (epoch : Nat)
  | secret (pk seed : ByteArray)
  | name (n : Nat) (name sig : ByteArray)
  | abandon
  | key (c k : ByteArray)
  | chunk (root : ByteArray) (len index : Nat) (slice : ByteArray) (sibs : List ByteArray)
  | receive (k : Nat)
  deriving DecidableEq, Inhabited

/-! ## Bytes -/

def decAs {α β} [Codec α] (f : α → β) (bs : List UInt8) : Option (β × List UInt8) :=
  match (dec bs : Option (α × List UInt8)) with
  | none => none
  | some (a, r) => some (f a, r)

theorem decAs_enc {α β} [Codec α] (f : α → β) (a : α) (rest : List UInt8) :
    decAs f (enc a ++ rest) = some (f a, rest) := by
  unfold decAs; rw [Codec.round]

def Body.enc : Body → List UInt8
  | .root d e s => 0 :: Codec.enc (d, e, s)
  | .invite k l t s => 1 :: Codec.enc (k, l, t, s)
  | .request d e c b => 12 :: Codec.enc (d, e, c, b)
  | .grant s => 3 :: Codec.enc s
  | .remove s => 4 :: Codec.enc s
  | .post k t n tm s => 23 :: Codec.enc (k, t, n, tm, s)
  | .wrap k r b => 6 :: Codec.enc (k, r, b)
  | .profile n tm s => 7 :: Codec.enc (n, tm, s)
  | .attach r l k x s => 8 :: Codec.enc (r, l, k, x, s)
  | .react e tm s => 9 :: Codec.enc (e, tm, s)
  | .approve s => 10 :: Codec.enc s
  | .admit => [11]
  | .accept c d => 13 :: Codec.enc (c, d)
  | .joining c k hs r nm d n => 14 :: Codec.enc (c, k, hs, r, nm, d, n)
  | .secret pk seed => 15 :: Codec.enc (pk, seed)
  | .name n nm s => 16 :: Codec.enc (n, nm, s)
  | .abandon => [17]
  | .key c k => 18 :: Codec.enc (c, k)
  | .chunk r l i x p => 19 :: Codec.enc (r, l, i, x, p)
  | .receive k => 24 :: Codec.enc k

def Body.dec : List UInt8 → Option (Body × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B) => Body.root p.1 p.2.1 p.2.2) r
  | 1 :: r => decAs (fun (p : B × Bool × Nat × B) => Body.invite p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 3 :: r => decAs (fun (p : B) => Body.grant p) r
  | 4 :: r => decAs (fun (p : B) => Body.remove p) r
  | 6 :: r => decAs (fun (p : B × B × B) => Body.wrap p.1 p.2.1 p.2.2) r
  | 7 :: r => decAs (fun (p : B × Nat × B) => Body.profile p.1 p.2.1 p.2.2) r
  | 8 :: r => decAs (fun (p : B × Nat × B × B × B) =>
      Body.attach p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 9 :: r => decAs (fun (p : B × Nat × B) => Body.react p.1 p.2.1 p.2.2) r
  | 10 :: r => decAs (fun (p : B) => Body.approve p) r
  | 11 :: r => some (.admit, r)
  | 12 :: r => decAs (fun (p : B × B × B × B) => Body.request p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 13 :: r => decAs (fun (p : B × B) => Body.accept p.1 p.2) r
  | 14 :: r => decAs (fun (p : B × B × List B × B × B × B × Nat) =>
      Body.joining p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) r
  | 15 :: r => decAs (fun (p : B × B) => Body.secret p.1 p.2) r
  | 16 :: r => decAs (fun (p : Nat × B × B) => Body.name p.1 p.2.1 p.2.2) r
  | 17 :: r => some (.abandon, r)
  | 18 :: r => decAs (fun (p : B × B) => Body.key p.1 p.2) r
  | 19 :: r => decAs (fun (p : B × Nat × Nat × B × List B) =>
      Body.chunk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 23 :: r => decAs (fun (p : B × B × Nat × Nat × B) =>
      Body.post p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 24 :: r => decAs (fun (p : Nat) => Body.receive p) r
  | _ => none

/-- `Body.enc`, as it runs: appended to a buffer (`Engine.Codec`). -/
def Body.encInto (buf : ByteArray) : Body → ByteArray
  | .root d e s => Codec.encInto (buf.push 0) (d, e, s)
  | .invite k l t s => Codec.encInto (buf.push 1) (k, l, t, s)
  | .request d e c b => Codec.encInto (buf.push 12) (d, e, c, b)
  | .grant s => Codec.encInto (buf.push 3) s
  | .remove s => Codec.encInto (buf.push 4) s
  | .post k t n tm s => Codec.encInto (buf.push 23) (k, t, n, tm, s)
  | .wrap k r b => Codec.encInto (buf.push 6) (k, r, b)
  | .profile n tm s => Codec.encInto (buf.push 7) (n, tm, s)
  | .attach r l k x s => Codec.encInto (buf.push 8) (r, l, k, x, s)
  | .react e tm s => Codec.encInto (buf.push 9) (e, tm, s)
  | .approve s => Codec.encInto (buf.push 10) s
  | .admit => buf.push 11
  | .accept c d => Codec.encInto (buf.push 13) (c, d)
  | .joining c k hs r nm d n => Codec.encInto (buf.push 14) (c, k, hs, r, nm, d, n)
  | .secret pk seed => Codec.encInto (buf.push 15) (pk, seed)
  | .name n nm s => Codec.encInto (buf.push 16) (n, nm, s)
  | .abandon => buf.push 17
  | .key c k => Codec.encInto (buf.push 18) (c, k)
  | .chunk r l i x p => Codec.encInto (buf.push 19) (r, l, i, x, p)
  | .receive k => Codec.encInto (buf.push 24) k

/-- `Body.dec`, as it runs: read at offset i of a byte array. -/
def Body.decFrom (b : ByteArray) (i : Nat) : Option (Body × Nat) :=
  match b[i]? with
  | some 0 => decFromAs (fun (p : B × B × B) => Body.root p.1 p.2.1 p.2.2) b (i + 1)
  | some 1 => decFromAs (fun (p : B × Bool × Nat × B) => Body.invite p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | some 3 => decFromAs (fun (p : B) => Body.grant p) b (i + 1)
  | some 4 => decFromAs (fun (p : B) => Body.remove p) b (i + 1)
  | some 6 => decFromAs (fun (p : B × B × B) => Body.wrap p.1 p.2.1 p.2.2) b (i + 1)
  | some 7 => decFromAs (fun (p : B × Nat × B) => Body.profile p.1 p.2.1 p.2.2) b (i + 1)
  | some 8 => decFromAs (fun (p : B × Nat × B × B × B) =>
      Body.attach p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 9 => decFromAs (fun (p : B × Nat × B) => Body.react p.1 p.2.1 p.2.2) b (i + 1)
  | some 10 => decFromAs (fun (p : B) => Body.approve p) b (i + 1)
  | some 11 => some (.admit, i + 1)
  | some 12 => decFromAs (fun (p : B × B × B × B) => Body.request p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | some 13 => decFromAs (fun (p : B × B) => Body.accept p.1 p.2) b (i + 1)
  | some 14 => decFromAs (fun (p : B × B × List B × B × B × B × Nat) =>
      Body.joining p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) b (i + 1)
  | some 15 => decFromAs (fun (p : B × B) => Body.secret p.1 p.2) b (i + 1)
  | some 16 => decFromAs (fun (p : Nat × B × B) => Body.name p.1 p.2.1 p.2.2) b (i + 1)
  | some 17 => some (.abandon, i + 1)
  | some 18 => decFromAs (fun (p : B × B) => Body.key p.1 p.2) b (i + 1)
  | some 19 => decFromAs (fun (p : B × Nat × Nat × B × List B) =>
      Body.chunk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 23 => decFromAs (fun (p : B × B × Nat × Nat × B) =>
      Body.post p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 24 => decFromAs (fun (p : Nat) => Body.receive p) b (i + 1)
  | _ => none

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round b rest := by
    cases b <;> simp only [Body.enc, Body.dec, List.cons_append] <;>
      first | rfl | exact decAs_enc _ _ _
  encInto := Body.encInto
  encInto_eq buf x := by
    cases x <;> simp only [Body.encInto, Body.enc] <;> first | exact encInto_tag .. | exact push_toList ..
  decFrom := Body.decFrom
  decFrom_at x h := by
    cases x <;> simp only [Body.enc] at h <;> simp only [Body.decFrom, h.tag] <;>
      first | exact decFromAs_tag _ h | rfl

def Fact.enc : Fact → List UInt8
  | .admission c u d e => 0 :: Codec.enc (c, u, d, e)
  | .invitation c i k l t => 1 :: Codec.enc (c, i, k, l, t)
  | .admin c u => 2 :: Codec.enc (c, u)
  | .removal c u b => 3 :: Codec.enc (c, u, b)
  | .message c u d k t n tm => 21 :: Codec.enc (c, u, d, k, t, n, tm)
  | .wrap c k r b => 5 :: Codec.enc (c, k, r, b)
  | .profile c u n tm => 6 :: Codec.enc (c, u, n, tm)
  | .attachment c m u r l k x => 7 :: Codec.enc (c, m, u, r, l, k, x)
  | .react c u t e tm => 8 :: Codec.enc (c, u, t, e, tm)
  | .request c u d e l t => 9 :: Codec.enc (c, u, d, e, l, t)
  | .approval c r u => 10 :: Codec.enc (c, r, u)
  | .secret pk seed => 11 :: Codec.enc (pk, seed)
  | .accepted c d => 12 :: Codec.enc (c, d)
  | .joining c k hs r nm d n => 13 :: Codec.enc (c, k, hs, r, nm, d, n)
  | .named c u nm n => 14 :: Codec.enc (c, u, nm, n)
  | .abandoned c r j => 15 :: Codec.enc (c, r, j)
  | .key c i k => 16 :: Codec.enc (c, i, k)
  | .chunk c a r l i => 17 :: Codec.enc (c, a, r, l, i)
  | .received c k m n => 22 :: Codec.enc (c, k, m, n)

def Fact.dec : List UInt8 → Option (Fact × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B × B) => Fact.admission p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 1 :: r => decAs (fun (p : B × B × B × Bool × Nat) =>
      Fact.invitation p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 2 :: r => decAs (fun (p : B × B) => Fact.admin p.1 p.2) r
  | 3 :: r => decAs (fun (p : B × B × B) => Fact.removal p.1 p.2.1 p.2.2) r
  | 5 :: r => decAs (fun (p : B × B × B × B) => Fact.wrap p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 6 :: r => decAs (fun (p : B × B × B × Nat) => Fact.profile p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 7 :: r => decAs (fun (p : B × B × B × B × Nat × B × B) =>
      Fact.attachment p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) r
  | 8 :: r => decAs (fun (p : B × B × B × B × Nat) => Fact.react p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 9 :: r => decAs (fun (p : B × B × B × B × Bool × Nat) =>
      Fact.request p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) r
  | 10 :: r => decAs (fun (p : B × B × B) => Fact.approval p.1 p.2.1 p.2.2) r
  | 11 :: r => decAs (fun (p : B × B) => Fact.secret p.1 p.2) r
  | 12 :: r => decAs (fun (p : B × B) => Fact.accepted p.1 p.2) r
  | 13 :: r => decAs (fun (p : B × B × List B × B × B × B × Nat) =>
      Fact.joining p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) r
  | 14 :: r => decAs (fun (p : B × B × B × Nat) => Fact.named p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 15 :: r => decAs (fun (p : B × B × B) => Fact.abandoned p.1 p.2.1 p.2.2) r
  | 16 :: r => decAs (fun (p : B × B × B) => Fact.key p.1 p.2.1 p.2.2) r
  | 17 :: r => decAs (fun (p : B × B × B × Nat × Nat) => Fact.chunk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 21 :: r => decAs (fun (p : B × B × B × B × B × Nat × Nat) =>
      Fact.message p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) r
  | 22 :: r => decAs (fun (p : B × B × B × Nat) => Fact.received p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | _ => none

/-- `Fact.enc`, as it runs: appended to a buffer (`Engine.Codec`). -/
def Fact.encInto (buf : ByteArray) : Fact → ByteArray
  | .admission c u d e => Codec.encInto (buf.push 0) (c, u, d, e)
  | .invitation c i k l t => Codec.encInto (buf.push 1) (c, i, k, l, t)
  | .admin c u => Codec.encInto (buf.push 2) (c, u)
  | .removal c u b => Codec.encInto (buf.push 3) (c, u, b)
  | .message c u d k t n tm => Codec.encInto (buf.push 21) (c, u, d, k, t, n, tm)
  | .wrap c k r b => Codec.encInto (buf.push 5) (c, k, r, b)
  | .profile c u n tm => Codec.encInto (buf.push 6) (c, u, n, tm)
  | .attachment c m u r l k x => Codec.encInto (buf.push 7) (c, m, u, r, l, k, x)
  | .react c u t e tm => Codec.encInto (buf.push 8) (c, u, t, e, tm)
  | .request c u d e l t => Codec.encInto (buf.push 9) (c, u, d, e, l, t)
  | .approval c r u => Codec.encInto (buf.push 10) (c, r, u)
  | .secret pk seed => Codec.encInto (buf.push 11) (pk, seed)
  | .accepted c d => Codec.encInto (buf.push 12) (c, d)
  | .joining c k hs r nm d n => Codec.encInto (buf.push 13) (c, k, hs, r, nm, d, n)
  | .named c u nm n => Codec.encInto (buf.push 14) (c, u, nm, n)
  | .abandoned c r j => Codec.encInto (buf.push 15) (c, r, j)
  | .key c i k => Codec.encInto (buf.push 16) (c, i, k)
  | .chunk c a r l i => Codec.encInto (buf.push 17) (c, a, r, l, i)
  | .received c k m n => Codec.encInto (buf.push 22) (c, k, m, n)

/-- `Fact.dec`, as it runs: read at offset i of a byte array. -/
def Fact.decFrom (b : ByteArray) (i : Nat) : Option (Fact × Nat) :=
  match b[i]? with
  | some 0 => decFromAs (fun (p : B × B × B × B) => Fact.admission p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | some 1 => decFromAs (fun (p : B × B × B × Bool × Nat) =>
      Fact.invitation p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 2 => decFromAs (fun (p : B × B) => Fact.admin p.1 p.2) b (i + 1)
  | some 3 => decFromAs (fun (p : B × B × B) => Fact.removal p.1 p.2.1 p.2.2) b (i + 1)
  | some 5 => decFromAs (fun (p : B × B × B × B) => Fact.wrap p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | some 6 => decFromAs (fun (p : B × B × B × Nat) => Fact.profile p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | some 7 => decFromAs (fun (p : B × B × B × B × Nat × B × B) =>
      Fact.attachment p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) b (i + 1)
  | some 8 => decFromAs (fun (p : B × B × B × B × Nat) => Fact.react p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 9 => decFromAs (fun (p : B × B × B × B × Bool × Nat) =>
      Fact.request p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) b (i + 1)
  | some 10 => decFromAs (fun (p : B × B × B) => Fact.approval p.1 p.2.1 p.2.2) b (i + 1)
  | some 11 => decFromAs (fun (p : B × B) => Fact.secret p.1 p.2) b (i + 1)
  | some 12 => decFromAs (fun (p : B × B) => Fact.accepted p.1 p.2) b (i + 1)
  | some 13 => decFromAs (fun (p : B × B × List B × B × B × B × Nat) =>
      Fact.joining p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) b (i + 1)
  | some 14 => decFromAs (fun (p : B × B × B × Nat) => Fact.named p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | some 15 => decFromAs (fun (p : B × B × B) => Fact.abandoned p.1 p.2.1 p.2.2) b (i + 1)
  | some 16 => decFromAs (fun (p : B × B × B) => Fact.key p.1 p.2.1 p.2.2) b (i + 1)
  | some 17 => decFromAs (fun (p : B × B × B × Nat × Nat) => Fact.chunk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 21 => decFromAs (fun (p : B × B × B × B × B × Nat × Nat) =>
      Fact.message p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) b (i + 1)
  | some 22 => decFromAs (fun (p : B × B × B × Nat) => Fact.received p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | _ => none

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round f rest := by
    cases f <;> simp only [Fact.enc, Fact.dec, List.cons_append] <;> exact decAs_enc _ _ _
  encInto := Fact.encInto
  encInto_eq buf x := by
    cases x <;> simp only [Fact.encInto, Fact.enc] <;> first | exact encInto_tag .. | exact push_toList ..
  decFrom := Fact.decFrom
  decFrom_at x h := by
    cases x <;> simp only [Fact.enc] at h <;> simp only [Fact.decFrom, h.tag] <;>
      first | exact decFromAs_tag _ h | rfl

/-! ## Signing -/

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned : Body → Body
  | .root d e _ => .root d e .empty
  | .invite k l t _ => .invite k l t .empty
  | .request d e _ _ => .request d e .empty .empty
  | .grant _ => .grant .empty
  | .remove _ => .remove .empty
  | .post k t n tm _ => .post k t n tm .empty
  | .profile n tm _ => .profile n tm .empty
  | .attach r l k x _ => .attach r l k x .empty
  | .react e tm _ => .react e tm .empty
  | .approve _ => .approve .empty
  | .name n nm _ => .name n nm .empty
  | b => b

/-- The bytes a signature on an op covers: a domain tag, the op's
requirements (its community first) and its unsigned body. -/
def signed (o : Op) (b : Body) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, o.reqs, b.unsigned)

/-! ## Validity -/

/-- Whether a fact is this device's own: local ops' facts, never
shared, never read by a shared op's validator (`check_reads_shared`). -/
def Fact.isLocal : Fact → Bool
  | .secret .. | .accepted .. | .joining .. | .abandoned .. | .key .. | .received .. => true
  | _ => false

/-- The largest file an attachment may name: 64 MiB of ciphertext. -/
def maxFile : Nat := 64 * 1024 * 1024

/-- The largest sealed attachment body: an 8 KiB preview, its fields,
and the seal. -/
def maxSealedMeta : Nat := 9 * 1024

/-- Whether a fact shows that user u of community c is admin: the
founder's admission (the founder's user is the community), or a grant. -/
def isAdmin (c u : Id) : Fact → Bool
  | .admission c' u' _ _ => decide (c' = c ∧ u' = c ∧ u = c)
  | .admin c' u' => decide (c' = c ∧ u' = u)
  | _ => false

/-- The counter cap: a post claiming this or more is saturated, and is
ordered by this device's receipt of it (`received`). Below 2^64, so a
counter and the cap fit the 8 bytes a sort key gives them. -/
def countCap : Nat := 2 ^ 63

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
    -- A self-removal needs no admin, but its third slot must still be a
    -- shared fact: a shared op never reads this device's own state.
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ ((t = u ∧ auth.isLocal = false) ∨ isAdmin c u auth) ∧
      C.verify d (signed o (.remove s)) s
    then some (.removal c t u) else none
  | .post k txt n tm s, [.admission c u0 _ _, .admission c1 u d _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ C.verify d (signed o (.post k txt n tm s)) s
    then some (.message c u d k txt n tm) else none
  | .profile n tm s, [.admission c u0 _ _, .admission c1 u d _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ n.size ≤ 64 ∧ C.verify d (signed o (.profile n tm s)) s
    then some (.profile c u n tm) else none
  -- An attachment: a child of a message, by its author's user.
  | .attach r l k x s, [.admission c u0 _ _, .admission c1 u d _, .message c2 u2 _ _ _ _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ u2 = u ∧ r.size = 32 ∧ 0 < l ∧
      l ≤ maxFile ∧ x.size ≤ maxSealedMeta ∧ C.verify d (signed o (.attach r l k x s)) s
    then some (.attachment c (o.reqs.getD 2 .empty) u r l k x) else none
  -- A chunk is its attachment's: it names the attachment's root and
  -- length, and authenticates itself against them.
  | .chunk r l i x p, [.admission c u0 _ _, .attachment c2 _ _ r2 l2 _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c2 = c ∧ r = r2 ∧ l = l2 ∧ Merkle.verify sha256 r l i x p = true
    then some (.chunk c (o.reqs.getD 1 .empty) r l i) else none
  | .react e tm s, [.admission c u0 _ _, .admission c1 u d _, .message c2 _ _ _ _ _ _] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ 0 < e.size ∧ e.size ≤ 32 ∧
      C.verify d (signed o (.react e tm s)) s
    then some (.react c u (o.reqs.getD 2 .empty) e tm) else none
  -- A wrap serves the admission in slot 1: it is to that admission's key.
  | .wrap k r bx, [.admission c u0 _ _, .admission c1 _ _ e] =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ r = e then some (.wrap c k r bx) else none
  | .secret pk seed, [] => if C.pub seed = pk then some (.secret pk seed) else none
  | .key c k, [] => if k.size = 32 then some (.key c (kidOf cryptoSeal k) k) else none
  | .accept c d, [] => some (.accepted c d)
  | .joining c k hs r nm d n, [] => some (.joining c k hs r nm d n)
  | .abandon, [.joining c _ _ r _ _ _] => some (.abandoned c r (o.reqs.headD .empty))
  -- This device's receipt of a saturated post: local, so it may read
  -- what it cites, and its counter is the writer's (`receiptFor`).
  | .receive k, [.message c _ _ kid _ n _] =>
    if countCap ≤ n then some (.received c kid (o.reqs.headD .empty) k) else none
  | .name n nm s, .admission c u0 _ _ :: .admission c1 u d _ :: auth :: prev =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ isAdmin c u auth ∧ nm.size ≤ 64 ∧
      counterOk c n prev = true ∧ C.verify d (signed o (.name n nm s)) s
    then some (.named c u nm n) else none
  | _, _ => none

/-- Each body's op type. -/
def Body.tag : Body → UInt8
  | .root .. => 0 | .invite .. => 1 | .request .. => 12 | .grant .. => 3
  | .remove .. => 4 | .wrap .. => 6
  | .profile .. => 7 | .attach .. => 8 | .react .. => 9
  | .approve .. => 10 | .admit => 11
  | .accept .. => 13 | .joining .. => 14 | .secret .. => 15 | .name .. => 16 | .abandon => 17
  | .key .. => 18 | .chunk .. => 19 | .post .. => 23 | .receive .. => 24

/-- An op's verdict: its body's, if its type is its body's. The type is
in the bytes its id hashes, so an op re-sent under another type would be
another op with the same fact: a message shown twice, a chunk counted
twice (`op_of_valid`). -/
def validate (C : Crypto) (o : Op) (fs : List Fact) : Option Fact :=
  match (decode o.body : Option Body) with
  | none => none
  | some b => if o.kind = b.tag then check C o b fs else none

/-! ## Relations: the lists facts are filed in, by name -/

namespace admission
/-- A device's admissions: whom `allowPeer` asks about. -/
def byDevice : Rel Fact := ⟨"admission", "byDevice", fun | .admission c _ d _ => some [c, d] | _ => none⟩
/-- A community's admissions: whom to dial and seal to. -/
def all : Rel Fact := ⟨"admission", "all", fun | .admission c .. => some [c] | _ => none⟩
/-- A user's admissions (its devices): whom a removal cites. -/
def byUser : Rel Fact := ⟨"admission", "byUser", fun | .admission c u .. => some [c, u] | _ => none⟩
end admission

namespace removal
def byUser : Rel Fact := ⟨"removal", "byUser", fun | .removal c u _ => some [c, u] | _ => none⟩
end removal

namespace admin
def byUser : Rel Fact := ⟨"admin", "byUser", fun | .admin c u => some [c, u] | _ => none⟩
end admin

namespace message
/-- A channel's messages, saturated ones included: the first, newest
first, has the highest counter (`topCount`). -/
def all : Rel Fact := ⟨"message", "all", fun | .message c .. => some [c] | _ => none⟩
def byAuthor : Rel Fact := ⟨"message", "byAuthor", fun | .message c u .. => some [c, u] | _ => none⟩
/-- A community's messages sealed under content key kid, below the
counter cap: a device lists the ones it can read as the union over the
keys it holds, its receipts of saturated ones after them (`readable`). -/
def byKey : Rel Fact :=
  ⟨"message", "byKey", fun | .message c _ _ k _ n _ => if n < countCap then some [c, k] else none | _ => none⟩
end message

namespace received
/-- This device's receipts of c's saturated messages under content key
kid, in the order it received them: where `readable` lists them. -/
def byKey : Rel Fact := ⟨"received", "byKey", fun | .received c k .. => some [c, k] | _ => none⟩
/-- This device's receipts in c: the newest one's counter is the next
one's less one (`topReceived`). -/
def all : Rel Fact := ⟨"received", "all", fun | .received c .. => some [c] | _ => none⟩
/-- Whether this device has received message m. -/
def byMsg : Rel Fact := ⟨"received", "byMsg", fun | .received _ _ m _ => some [m] | _ => none⟩
end received

namespace wrap
def byContentKey : Rel Fact := ⟨"wrap", "byContentKey", fun | .wrap c k _ _ => some [c, k] | _ => none⟩
/-- The keys wrapped to a device's X25519 key in c. -/
def byRecipient : Rel Fact := ⟨"wrap", "byRecipient", fun | .wrap c _ r _ => some [c, r] | _ => none⟩
end wrap

namespace key
/-- This device's content keys for c (local). -/
def byCommunity : Rel Fact := ⟨"key", "byCommunity", fun | .key c .. => some [c] | _ => none⟩
/-- This device's content key by id (local). -/
def byId : Rel Fact := ⟨"key", "byId", fun | .key _ i _ => some [i] | _ => none⟩
end key

/-- A space of any kind (Unicode's White_Space): each draws as blank. -/
def isBlank (c : UInt32) : Bool :=
  c == 32 || Text.inRange c 9 13 || c == 0x85 || c == 0xA0 || c == 0x1680 ||
  Text.inRange c 0x2000 0x200A || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000

/-- What a name looks like: its words, without the characters drawn as
nothing (`Text.isInvisible`), split at spaces of any kind and joined by
one space. Two users whose names look alike by it are namesakes, and
both are marked (Kinds.Profile.namesake). -/
def look (s : String) : List UInt32 :=
  [32].intercalate ((((s.toList.map (·.val)).filter (!Text.isInvisible ·)).splitOnP isBlank).filter (!·.isEmpty))

def nameLook (s : String) : ByteArray := (String.mk ((look s).map fun c => Char.ofNat c.toNat)).toUTF8

namespace profile
def byUser : Rel Fact := ⟨"profile", "byUser", fun | .profile c u .. => some [c, u] | _ => none⟩
def all : Rel Fact := ⟨"profile", "all", fun | .profile c .. => some [c] | _ => none⟩
/-- By how the name looks: a name's namesakes. -/
def byLook : Rel Fact :=
  ⟨"profile", "byLook", fun | .profile c _ n _ => some [c, nameLook ((String.fromUTF8? n).getD "?")] | _ => none⟩
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
def byRequest : Rel Fact := ⟨"abandoned", "byRequest", fun | .abandoned _ r _ => some [r] | _ => none⟩
/-- Whether this joining op was stopped. -/
def byJoining : Rel Fact := ⟨"abandoned", "byJoining", fun | .abandoned _ _ j => some [j] | _ => none⟩
end abandoned

namespace named
/-- A community's names, by counter: the current one is the list read
newest first, limit 1. -/
def current : Rel Fact := ⟨"named", "current", fun | .named c .. => some [c] | _ => none⟩
end named

namespace attachment
/-- A message's attachments: what its components list. -/
def byMessage : Rel Fact := ⟨"attachment", "byMessage", fun | .attachment c m .. => some [c, m] | _ => none⟩
end attachment

namespace chunk
/-- An attachment's chunks, by index: their count is the download's
progress (`Community.progress`); read in order, they assemble the file. -/
def byAttachment : Rel Fact :=
  ⟨"chunk", "byAttachment", fun | .chunk c a .. => some [c, a] | _ => none⟩
end chunk

/-- Every relation of the community's facts. Invitations are in none
(read by their own key). -/
def rels : List (Rel Fact) :=
  [admission.byDevice, admission.all, admission.byUser, removal.byUser, admin.byUser, message.all, message.byAuthor,
   message.byKey, received.byKey, received.all, received.byMsg,
   wrap.byContentKey, profile.byUser, profile.all, profile.byLook, react.byMessage, react.byMessageEmoji,
   request.all, approval.byRequest, secret.byKey, secret.all, accepted.all, joining.all, named.current,
   abandoned.byRequest, abandoned.byJoining, wrap.byRecipient, key.byCommunity, key.byId, attachment.byMessage,
   chunk.byAttachment]

/-- The keys a fact is filed under: its relations'. -/
def keys : Fact → List ByteArray := keysOf rels

/-- A number as 8 bytes, most significant first, so byte order is
numeric order. -/
def be64 (n : Nat) : ByteArray := ByteArray.mk ((List.range 8).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray

/-- The largest time a sort key tells apart: later claims sort as it. -/
def timeCap : Nat := 2 ^ 64 - 1

/-- A message's sort key: its counter, then its time, each capped, so
the order is (counter, time, id) (`msg_cmp`). -/
def msgKey (n tm : Nat) : ByteArray := be64 (min n countCap) ++ be64 (min tm timeCap)

/-- A receipt's sort key: after every counter below the cap, then by
this device's receipt counter, then by the message. -/
def recKey (k : Nat) (m : Id) : ByteArray := be64 countCap ++ be64 k ++ m

/-- Where a fact sorts under its keys: messages by counter and time,
receipts by arrival, other timed facts by time (ties by id). -/
def sortOf : Fact → ByteArray
  | .message _ _ _ _ _ n tm => msgKey n tm
  | .received _ _ m k => recKey k m
  | .profile _ _ _ tm => be64 tm
  | .chunk _ _ _ _ i => be64 i
  | .react _ _ _ _ tm => be64 tm
  | .named _ _ _ n => be64 n
  | _ => .empty

instance : SortKey Fact := ⟨sortOf⟩

/-- Whether an op is local, from its body: a device's secrets, its
acceptances and its joins are, never sent or taken; everything else is
shared in its community. -/
def Body.isLocal : Body → Bool
  | .secret .. | .accept .. | .joining .. | .abandon | .key .. | .receive .. => true
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
admissions, removals, ...), which every window includes. A post's
counter does not feed it: sync's windows are over every timed kind in a
room, and only time is common to them, in minutes that mean the same on
every device; a counter orders one channel's messages only, and one
claim can saturate it. -/
def orderOf (o : Op) : Nat :=
  match (decode o.body : Option Body) with
  | some (.post _ _ _ t _) | some (.profile _ t _) | some (.react _ t _) => t
  | _ => 0

def family (C : Crypto) : Family Fact :=
  { validate := validate C, keys, scope := scopeOf, order := orderOf }

end Community
