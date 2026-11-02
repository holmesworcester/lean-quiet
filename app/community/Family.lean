import engine.core.Order
import app.community.Op
import app.community.Validate
import app.community.channel.message.Op
import app.community.channel.message.Validate
import app.community.channel.message.attachment.Op
import app.community.channel.message.attachment.Validate
import app.community.channel.message.attachment.chunk.Op
import app.community.channel.message.attachment.chunk.Validate
import app.community.channel.message.reaction.Op
import app.community.channel.message.reaction.Validate
import app.community.channel.message.receipt.Op
import app.community.channel.message.draft.Op
import app.community.channel.message.draft.Validate
import app.community.channel.message.receipt.Validate
import app.community.device.endpoint.Op
import app.community.device.endpoint.Validate
import app.community.device.secret.Op
import app.community.device.secret.Validate
import app.community.key.Op
import app.community.key.Validate
import app.community.key.wrap.Op
import app.community.key.wrap.Validate
import app.community.member.admin.Op
import app.community.member.admin.Validate
import app.community.member.invite.Op
import app.community.member.invite.Validate
import app.community.member.invite.request.Op
import app.community.member.invite.request.Validate
import app.community.member.invite.request.approve.Op
import app.community.member.invite.request.approve.Validate
import app.community.member.invite.request.approve.admit.Op
import app.community.member.invite.request.approve.admit.Validate
import app.community.member.join.accept.Op
import app.community.member.join.accept.Validate
import app.community.member.join.joining.Op
import app.community.member.join.joining.Validate
import app.community.member.join.joining.abandon.Op
import app.community.member.join.joining.abandon.Validate
import app.community.member.remove.Op
import app.community.member.remove.Validate
import app.community.name.Op
import app.community.name.Validate
import app.community.profile.Op
import app.community.profile.Validate

/-
A community, after libquiet's DESIGN.md ("A user is its origin op",
"Invite, join, vouch") and its removal stack (#778, #98, #1088):

- The root founds the community; its fact is the founder's admission,
  and the founder's user is the community id. The founder is admin.
- An invite is issued by an admitted device. A request it carries is
  admitted by one approval (the user's decisions: 2026-10-27,
  approvals are always needed, and they are where key-material wraps to
  the new device hang; 2026-10-31, no thresholds, since one member can
  mint the distinct users any threshold would count). A link invitation
  (another device for the issuer's user) is approved by the issuer's
  user only, as libquiet's unbound device links are. There is no open
  link: the bearer key alone admits nobody.
- A request redeems an invitation: the requesting device consents
  (signs), and so does the invitation's bearer key from the link. A
  request admits nobody. It is libquiet's Join before its vouches.
- An approval is a member's signed yes to a request, by another device
  than the requester's; a link request is approved by the issuer's user
  only. It cites the request, so approvals come after the request
  without the engine needing forward needs.
- An admission of a request cites the request and exactly one
  approval of it. It is unsigned (anyone holding the approval may
  compose it), and its fact is the admission: into a new user named by
  the request for a member invitation, into the issuer's user for a link
  invitation. Several admits of one request (citing other approvals) all
  give that same admission fact.
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
  counts as a member. A device may be admitted into several users; it
  counts while none of them is removed, and removing any of them cuts it
  (docs/REMOVAL.md).
- A node's key is local (`endpoint`): 32 random bytes, one per node, its
  X25519 key pair. A root or request names it as the device's `enc`,
  under the device's signature, so an admission ties a device to the
  node it lives on. The node handshakes with it (the Connection family),
  and content keys wrapped to its devices open with it.
- A post is a message by an admitted device. Its body is sealed: it
  names a content key by id and carries the nonce and ciphertext
  (`Community.Keys`). Its header is clear: the key id, the time, the
  signature, which covers the sealed bytes. Validators read only the
  header, so a keyless node judges a post as a member does.
- A content key is local (`key`): this node's copy of a community's
  key. A wrap delivers one to a node's X25519 key, sealed so that only
  that node opens it. A wrap admits nobody, so it needs no author.
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
  file's Merkle root and length (`Merkle`); its body, sealed
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

Each op type is a folder below this one: its body and fact (Op.lean)
and its validator (Validate.lean). This file is the registry: the sum of
them all, the bytes of the sum, which validator judges which op, and the
lists the family files facts in.

Signatures are a parameter (`Crypto`), so the laws hold for any scheme;
what unforgeability buys is stated as a hypothesis where it is used.
-/

namespace Community
open Engine Codec

/-- A fact of the community family: one op type's fact. -/
inductive Fact where
  | ofAdmission (f : Root.Fact)
  | ofInvitation (f : Invitation.Fact)
  | ofAdmin (f : Grant.Fact)
  | ofRemoval (f : Remove.Fact)
  | ofMessage (f : Post.Fact)
  | ofWrap (f : Wrap.Fact)
  | ofProfile (f : Profile.Fact)
  | ofAttachment (f : Attach.Fact)
  | ofReact (f : React.Fact)
  | ofRequest (f : Request.Fact)
  | ofApproval (f : Approve.Fact)
  | ofSecret (f : Secret.Fact)
  | ofAccepted (f : Accept.Fact)
  | ofJoining (f : Joining.Fact)
  | ofNamed (f : Rename.Fact)
  | ofAbandoned (f : Abandon.Fact)
  | ofKey (f : ContentKey.Fact)
  | ofChunk (f : Chunk.Fact)
  | ofEndpoint (f : Endpoint.Fact)
  | ofReceived (f : Receive.Fact)
  | ofDraft (f : Draft.Fact)
  deriving DecidableEq, Inhabited

/-- An op of the community family: one op type's body. -/
inductive Body where
  | ofRoot (b : Root.Body)
  | ofInvite (b : Invitation.Body)
  | ofRequest (b : Request.Body)
  | ofGrant (b : Grant.Body)
  | ofRemove (b : Remove.Body)
  | ofPost (b : Post.Body)
  | ofWrap (b : Wrap.Body)
  | ofProfile (b : Profile.Body)
  | ofAttach (b : Attach.Body)
  | ofReact (b : React.Body)
  | ofApprove (b : Approve.Body)
  | ofAdmit (b : Admit.Body)
  | ofAccept (b : Accept.Body)
  | ofJoining (b : Joining.Body)
  | ofSecret (b : Secret.Body)
  | ofName (b : Rename.Body)
  | ofAbandon (b : Abandon.Body)
  | ofKey (b : ContentKey.Body)
  | ofChunk (b : Chunk.Body)
  | ofEndpoint (b : Endpoint.Body)
  | ofReceive (b : Receive.Body)
  | ofDraft (b : Draft.Body)
  deriving DecidableEq, Inhabited

/-! ## Each op type's fact and body by its fields, as laws and views match them -/

@[match_pattern] abbrev Fact.admission (c : Id) (u : Id) (device : Key) (enc : Key) : Fact := .ofAdmission ⟨c, u, device, enc⟩
@[match_pattern] abbrev Fact.invitation (c : Id) (issuer : Id) (bearer : Key) (link : Bool) : Fact := .ofInvitation ⟨c, issuer, bearer, link⟩
@[match_pattern] abbrev Fact.admin (c : Id) (u : Id) : Fact := .ofAdmin ⟨c, u⟩
@[match_pattern] abbrev Fact.removal (c : Id) (u : Id) (by_ : Id) : Fact := .ofRemoval ⟨c, u, by_⟩
@[match_pattern] abbrev Fact.message (c : Id) (u : Id) (device : ByteArray) (ckey : ByteArray) (text : ByteArray) (n : Nat) (time : Nat) (clump : Option Id := none) : Fact := .ofMessage ⟨c, u, device, ckey, text, n, time, clump⟩
@[match_pattern] abbrev Fact.wrap (c : Id) (ckey : ByteArray) (recipient : ByteArray) (box : ByteArray) : Fact := .ofWrap ⟨c, ckey, recipient, box⟩
@[match_pattern] abbrev Fact.profile (c : Id) (u : Id) (name : ByteArray) (time : Nat) : Fact := .ofProfile ⟨c, u, name, time⟩
@[match_pattern] abbrev Fact.attachment (c : Id) (msg : Id) (u : Id) (root : Id) (len : Nat) (time : Nat) (kid : ByteArray) (sealed : ByteArray) : Fact := .ofAttachment ⟨c, msg, u, root, len, time, kid, sealed⟩
@[match_pattern] abbrev Fact.react (c : Id) (u : Id) (target : Id) (emoji : ByteArray) (time : Nat) : Fact := .ofReact ⟨c, u, target, emoji, time⟩
@[match_pattern] abbrev Fact.request (c : Id) (u : Id) (device : Key) (enc : Key) (link : Bool) : Fact := .ofRequest ⟨c, u, device, enc, link⟩
@[match_pattern] abbrev Fact.approval (c : Id) (req : Id) (u : Id) : Fact := .ofApproval ⟨c, req, u⟩
@[match_pattern] abbrev Fact.secret (pk : ByteArray) (seed : ByteArray) : Fact := .ofSecret ⟨pk, seed⟩
@[match_pattern] abbrev Fact.accepted (c : Id) (device : Key) : Fact := .ofAccepted ⟨c, device⟩
@[match_pattern] abbrev Fact.joining (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray) (device : Key) (epoch : Nat) : Fact := .ofJoining ⟨c, inviter, hints, req, name, device, epoch⟩
@[match_pattern] abbrev Fact.named (c : Id) (u : Id) (name : ByteArray) (n : Nat) : Fact := .ofNamed ⟨c, u, name, n⟩
@[match_pattern] abbrev Fact.abandoned (c : Id) (req : Id) (join : Id) : Fact := .ofAbandoned ⟨c, req, join⟩
@[match_pattern] abbrev Fact.key (c : ByteArray) (kid : ByteArray) (k : ByteArray) : Fact := .ofKey ⟨c, kid, k⟩
@[match_pattern] abbrev Fact.chunk (c : Id) (att : Id) (root : Id) (len : Nat) (index : Nat) : Fact := .ofChunk ⟨c, att, root, len, index⟩
@[match_pattern] abbrev Fact.endpoint (pk : ByteArray) (sk : ByteArray) : Fact := .ofEndpoint ⟨pk, sk⟩
@[match_pattern] abbrev Fact.received (c : Id) (kid : Id) (msg : Id) (k : Nat) (clump : Option Id := none) : Fact := .ofReceived ⟨c, kid, msg, k, clump⟩

@[match_pattern] abbrev Body.root (device : ByteArray) (enc : ByteArray) (sig : ByteArray) : Body := .ofRoot ⟨device, enc, sig⟩
@[match_pattern] abbrev Body.invite (bearer : Key) (link : Bool) (sig : ByteArray) : Body := .ofInvite ⟨bearer, link, sig⟩
@[match_pattern] abbrev Body.request (device : ByteArray) (enc : ByteArray) (consent : ByteArray) (bearerSig : ByteArray) : Body := .ofRequest ⟨device, enc, consent, bearerSig⟩
@[match_pattern] abbrev Body.grant (sig : ByteArray) : Body := .ofGrant ⟨sig⟩
@[match_pattern] abbrev Body.remove (sig : ByteArray) : Body := .ofRemove ⟨sig⟩
@[match_pattern] abbrev Body.post (ckey : ByteArray) (text : ByteArray) (n : Nat) (time : Nat) (sig : ByteArray) : Body := .ofPost ⟨ckey, text, n, time, sig⟩
@[match_pattern] abbrev Body.wrap (ckey : ByteArray) (recipient : ByteArray) (box : ByteArray) : Body := .ofWrap ⟨ckey, recipient, box⟩
@[match_pattern] abbrev Body.profile (name : ByteArray) (time : Nat) (sig : ByteArray) : Body := .ofProfile ⟨name, time, sig⟩
@[match_pattern] abbrev Body.attach (root : ByteArray) (len : Nat) (time : Nat) (kid : ByteArray) (sealed : ByteArray) (sig : ByteArray) : Body := .ofAttach ⟨root, len, time, kid, sealed, sig⟩
@[match_pattern] abbrev Body.react (emoji : ByteArray) (time : Nat) (sig : ByteArray) : Body := .ofReact ⟨emoji, time, sig⟩
@[match_pattern] abbrev Body.approve (sig : ByteArray) : Body := .ofApprove ⟨sig⟩
@[match_pattern] abbrev Body.admit : Body := .ofAdmit {}
@[match_pattern] abbrev Body.accept (c : Id) (device : Key) : Body := .ofAccept ⟨c, device⟩
@[match_pattern] abbrev Body.joining (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray) (device : Key) (epoch : Nat) : Body := .ofJoining ⟨c, inviter, hints, req, name, device, epoch⟩
@[match_pattern] abbrev Body.secret (pk : ByteArray) (seed : ByteArray) : Body := .ofSecret ⟨pk, seed⟩
@[match_pattern] abbrev Body.name (n : Nat) (name : ByteArray) (sig : ByteArray) : Body := .ofName ⟨n, name, sig⟩
@[match_pattern] abbrev Body.abandon : Body := .ofAbandon {}
@[match_pattern] abbrev Body.key (c : ByteArray) (k : ByteArray) : Body := .ofKey ⟨c, k⟩
@[match_pattern] abbrev Body.chunk (root : ByteArray) (len : Nat) (time : Nat) (index : Nat) (slice : ByteArray) (sibs : List ByteArray) : Body := .ofChunk ⟨root, len, time, index, slice, sibs⟩
@[match_pattern] abbrev Body.endpoint (sk : ByteArray) : Body := .ofEndpoint ⟨sk⟩
@[match_pattern] abbrev Body.receive (k : Nat) : Body := .ofReceive ⟨k⟩

theorem Fact.admission.injEq (c : Id) (u : Id) (device : Key) (enc : Key) (c' : Id) (u' : Id) (device' : Key) (enc' : Key) :
    (Fact.admission c u device enc = Fact.admission c' u' device' enc') = (c = c' ∧ u = u' ∧ device = device' ∧ enc = enc') := by
  simp [Fact.admission]
theorem Fact.admission.inj {c : Id} {u : Id} {device : Key} {enc : Key} {c' : Id} {u' : Id} {device' : Key} {enc' : Key}
    (hinj : Fact.admission c u device enc = Fact.admission c' u' device' enc') : c = c' ∧ u = u' ∧ device = device' ∧ enc = enc' := by
  rw [Fact.admission.injEq] at hinj; exact hinj
theorem Fact.invitation.injEq (c : Id) (issuer : Id) (bearer : Key) (link : Bool) (c' : Id) (issuer' : Id) (bearer' : Key) (link' : Bool) :
    (Fact.invitation c issuer bearer link = Fact.invitation c' issuer' bearer' link') = (c = c' ∧ issuer = issuer' ∧ bearer = bearer' ∧ link = link') := by
  simp [Fact.invitation]
theorem Fact.invitation.inj {c : Id} {issuer : Id} {bearer : Key} {link : Bool} {c' : Id} {issuer' : Id} {bearer' : Key} {link' : Bool}
    (hinj : Fact.invitation c issuer bearer link = Fact.invitation c' issuer' bearer' link') : c = c' ∧ issuer = issuer' ∧ bearer = bearer' ∧ link = link' := by
  rw [Fact.invitation.injEq] at hinj; exact hinj
theorem Fact.admin.injEq (c : Id) (u : Id) (c' : Id) (u' : Id) :
    (Fact.admin c u = Fact.admin c' u') = (c = c' ∧ u = u') := by
  simp [Fact.admin]
theorem Fact.admin.inj {c : Id} {u : Id} {c' : Id} {u' : Id}
    (hinj : Fact.admin c u = Fact.admin c' u') : c = c' ∧ u = u' := by
  rw [Fact.admin.injEq] at hinj; exact hinj
theorem Fact.removal.injEq (c : Id) (u : Id) (by_ : Id) (c' : Id) (u' : Id) (by_' : Id) :
    (Fact.removal c u by_ = Fact.removal c' u' by_') = (c = c' ∧ u = u' ∧ by_ = by_') := by
  simp [Fact.removal]
theorem Fact.removal.inj {c : Id} {u : Id} {by_ : Id} {c' : Id} {u' : Id} {by_' : Id}
    (hinj : Fact.removal c u by_ = Fact.removal c' u' by_') : c = c' ∧ u = u' ∧ by_ = by_' := by
  rw [Fact.removal.injEq] at hinj; exact hinj
theorem Fact.message.injEq (c : Id) (u : Id) (device : ByteArray) (ckey : ByteArray) (text : ByteArray) (n : Nat) (time : Nat) (clump : Option Id) (c' : Id) (u' : Id) (device' : ByteArray) (ckey' : ByteArray) (text' : ByteArray) (n' : Nat) (time' : Nat) (clump' : Option Id) :
    (Fact.message c u device ckey text n time clump = Fact.message c' u' device' ckey' text' n' time' clump') = (c = c' ∧ u = u' ∧ device = device' ∧ ckey = ckey' ∧ text = text' ∧ n = n' ∧ time = time' ∧ clump = clump') := by
  simp [Fact.message]
theorem Fact.message.inj {c : Id} {u : Id} {device : ByteArray} {ckey : ByteArray} {text : ByteArray} {n : Nat} {time : Nat} {clump : Option Id} {c' : Id} {u' : Id} {device' : ByteArray} {ckey' : ByteArray} {text' : ByteArray} {n' : Nat} {time' : Nat} {clump' : Option Id}
    (hinj : Fact.message c u device ckey text n time clump = Fact.message c' u' device' ckey' text' n' time' clump') : c = c' ∧ u = u' ∧ device = device' ∧ ckey = ckey' ∧ text = text' ∧ n = n' ∧ time = time' ∧ clump = clump' := by
  rw [Fact.message.injEq] at hinj; exact hinj
theorem Fact.wrap.injEq (c : Id) (ckey : ByteArray) (recipient : ByteArray) (box : ByteArray) (c' : Id) (ckey' : ByteArray) (recipient' : ByteArray) (box' : ByteArray) :
    (Fact.wrap c ckey recipient box = Fact.wrap c' ckey' recipient' box') = (c = c' ∧ ckey = ckey' ∧ recipient = recipient' ∧ box = box') := by
  simp [Fact.wrap]
theorem Fact.wrap.inj {c : Id} {ckey : ByteArray} {recipient : ByteArray} {box : ByteArray} {c' : Id} {ckey' : ByteArray} {recipient' : ByteArray} {box' : ByteArray}
    (hinj : Fact.wrap c ckey recipient box = Fact.wrap c' ckey' recipient' box') : c = c' ∧ ckey = ckey' ∧ recipient = recipient' ∧ box = box' := by
  rw [Fact.wrap.injEq] at hinj; exact hinj
theorem Fact.profile.injEq (c : Id) (u : Id) (name : ByteArray) (time : Nat) (c' : Id) (u' : Id) (name' : ByteArray) (time' : Nat) :
    (Fact.profile c u name time = Fact.profile c' u' name' time') = (c = c' ∧ u = u' ∧ name = name' ∧ time = time') := by
  simp [Fact.profile]
theorem Fact.profile.inj {c : Id} {u : Id} {name : ByteArray} {time : Nat} {c' : Id} {u' : Id} {name' : ByteArray} {time' : Nat}
    (hinj : Fact.profile c u name time = Fact.profile c' u' name' time') : c = c' ∧ u = u' ∧ name = name' ∧ time = time' := by
  rw [Fact.profile.injEq] at hinj; exact hinj
theorem Fact.attachment.injEq (c : Id) (msg : Id) (u : Id) (root : Id) (len : Nat) (time : Nat) (kid : ByteArray) (sealed : ByteArray) (c' : Id) (msg' : Id) (u' : Id) (root' : Id) (len' : Nat) (time' : Nat) (kid' : ByteArray) (sealed' : ByteArray) :
    (Fact.attachment c msg u root len time kid sealed = Fact.attachment c' msg' u' root' len' time' kid' sealed') = (c = c' ∧ msg = msg' ∧ u = u' ∧ root = root' ∧ len = len' ∧ time = time' ∧ kid = kid' ∧ sealed = sealed') := by
  simp [Fact.attachment]
theorem Fact.attachment.inj {c : Id} {msg : Id} {u : Id} {root : Id} {len : Nat} {time : Nat} {kid : ByteArray} {sealed : ByteArray} {c' : Id} {msg' : Id} {u' : Id} {root' : Id} {len' : Nat} {time' : Nat} {kid' : ByteArray} {sealed' : ByteArray}
    (hinj : Fact.attachment c msg u root len time kid sealed = Fact.attachment c' msg' u' root' len' time' kid' sealed') : c = c' ∧ msg = msg' ∧ u = u' ∧ root = root' ∧ len = len' ∧ time = time' ∧ kid = kid' ∧ sealed = sealed' := by
  rw [Fact.attachment.injEq] at hinj; exact hinj
theorem Fact.react.injEq (c : Id) (u : Id) (target : Id) (emoji : ByteArray) (time : Nat) (c' : Id) (u' : Id) (target' : Id) (emoji' : ByteArray) (time' : Nat) :
    (Fact.react c u target emoji time = Fact.react c' u' target' emoji' time') = (c = c' ∧ u = u' ∧ target = target' ∧ emoji = emoji' ∧ time = time') := by
  simp [Fact.react]
theorem Fact.react.inj {c : Id} {u : Id} {target : Id} {emoji : ByteArray} {time : Nat} {c' : Id} {u' : Id} {target' : Id} {emoji' : ByteArray} {time' : Nat}
    (hinj : Fact.react c u target emoji time = Fact.react c' u' target' emoji' time') : c = c' ∧ u = u' ∧ target = target' ∧ emoji = emoji' ∧ time = time' := by
  rw [Fact.react.injEq] at hinj; exact hinj
theorem Fact.request.injEq (c : Id) (u : Id) (device : Key) (enc : Key) (link : Bool) (c' : Id) (u' : Id) (device' : Key) (enc' : Key) (link' : Bool) :
    (Fact.request c u device enc link = Fact.request c' u' device' enc' link') = (c = c' ∧ u = u' ∧ device = device' ∧ enc = enc' ∧ link = link') := by
  simp [Fact.request]
theorem Fact.request.inj {c : Id} {u : Id} {device : Key} {enc : Key} {link : Bool} {c' : Id} {u' : Id} {device' : Key} {enc' : Key} {link' : Bool}
    (hinj : Fact.request c u device enc link = Fact.request c' u' device' enc' link') : c = c' ∧ u = u' ∧ device = device' ∧ enc = enc' ∧ link = link' := by
  rw [Fact.request.injEq] at hinj; exact hinj
theorem Fact.approval.injEq (c : Id) (req : Id) (u : Id) (c' : Id) (req' : Id) (u' : Id) :
    (Fact.approval c req u = Fact.approval c' req' u') = (c = c' ∧ req = req' ∧ u = u') := by
  simp [Fact.approval]
theorem Fact.approval.inj {c : Id} {req : Id} {u : Id} {c' : Id} {req' : Id} {u' : Id}
    (hinj : Fact.approval c req u = Fact.approval c' req' u') : c = c' ∧ req = req' ∧ u = u' := by
  rw [Fact.approval.injEq] at hinj; exact hinj
theorem Fact.secret.injEq (pk : ByteArray) (seed : ByteArray) (pk' : ByteArray) (seed' : ByteArray) :
    (Fact.secret pk seed = Fact.secret pk' seed') = (pk = pk' ∧ seed = seed') := by
  simp [Fact.secret]
theorem Fact.secret.inj {pk : ByteArray} {seed : ByteArray} {pk' : ByteArray} {seed' : ByteArray}
    (hinj : Fact.secret pk seed = Fact.secret pk' seed') : pk = pk' ∧ seed = seed' := by
  rw [Fact.secret.injEq] at hinj; exact hinj
theorem Fact.accepted.injEq (c : Id) (device : Key) (c' : Id) (device' : Key) :
    (Fact.accepted c device = Fact.accepted c' device') = (c = c' ∧ device = device') := by
  simp [Fact.accepted]
theorem Fact.accepted.inj {c : Id} {device : Key} {c' : Id} {device' : Key}
    (hinj : Fact.accepted c device = Fact.accepted c' device') : c = c' ∧ device = device' := by
  rw [Fact.accepted.injEq] at hinj; exact hinj
theorem Fact.joining.injEq (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray) (device : Key) (epoch : Nat) (c' : Id) (inviter' : Key) (hints' : List ByteArray) (req' : Id) (name' : ByteArray) (device' : Key) (epoch' : Nat) :
    (Fact.joining c inviter hints req name device epoch = Fact.joining c' inviter' hints' req' name' device' epoch') = (c = c' ∧ inviter = inviter' ∧ hints = hints' ∧ req = req' ∧ name = name' ∧ device = device' ∧ epoch = epoch') := by
  simp [Fact.joining]
theorem Fact.joining.inj {c : Id} {inviter : Key} {hints : List ByteArray} {req : Id} {name : ByteArray} {device : Key} {epoch : Nat} {c' : Id} {inviter' : Key} {hints' : List ByteArray} {req' : Id} {name' : ByteArray} {device' : Key} {epoch' : Nat}
    (hinj : Fact.joining c inviter hints req name device epoch = Fact.joining c' inviter' hints' req' name' device' epoch') : c = c' ∧ inviter = inviter' ∧ hints = hints' ∧ req = req' ∧ name = name' ∧ device = device' ∧ epoch = epoch' := by
  rw [Fact.joining.injEq] at hinj; exact hinj
theorem Fact.named.injEq (c : Id) (u : Id) (name : ByteArray) (n : Nat) (c' : Id) (u' : Id) (name' : ByteArray) (n' : Nat) :
    (Fact.named c u name n = Fact.named c' u' name' n') = (c = c' ∧ u = u' ∧ name = name' ∧ n = n') := by
  simp [Fact.named]
theorem Fact.named.inj {c : Id} {u : Id} {name : ByteArray} {n : Nat} {c' : Id} {u' : Id} {name' : ByteArray} {n' : Nat}
    (hinj : Fact.named c u name n = Fact.named c' u' name' n') : c = c' ∧ u = u' ∧ name = name' ∧ n = n' := by
  rw [Fact.named.injEq] at hinj; exact hinj
theorem Fact.abandoned.injEq (c : Id) (req : Id) (join : Id) (c' : Id) (req' : Id) (join' : Id) :
    (Fact.abandoned c req join = Fact.abandoned c' req' join') = (c = c' ∧ req = req' ∧ join = join') := by
  simp [Fact.abandoned]
theorem Fact.abandoned.inj {c : Id} {req : Id} {join : Id} {c' : Id} {req' : Id} {join' : Id}
    (hinj : Fact.abandoned c req join = Fact.abandoned c' req' join') : c = c' ∧ req = req' ∧ join = join' := by
  rw [Fact.abandoned.injEq] at hinj; exact hinj
theorem Fact.key.injEq (c : ByteArray) (kid : ByteArray) (k : ByteArray) (c' : ByteArray) (kid' : ByteArray) (k' : ByteArray) :
    (Fact.key c kid k = Fact.key c' kid' k') = (c = c' ∧ kid = kid' ∧ k = k') := by
  simp [Fact.key]
theorem Fact.key.inj {c : ByteArray} {kid : ByteArray} {k : ByteArray} {c' : ByteArray} {kid' : ByteArray} {k' : ByteArray}
    (hinj : Fact.key c kid k = Fact.key c' kid' k') : c = c' ∧ kid = kid' ∧ k = k' := by
  rw [Fact.key.injEq] at hinj; exact hinj
theorem Fact.chunk.injEq (c : Id) (att : Id) (root : Id) (len : Nat) (index : Nat) (c' : Id) (att' : Id) (root' : Id) (len' : Nat) (index' : Nat) :
    (Fact.chunk c att root len index = Fact.chunk c' att' root' len' index') = (c = c' ∧ att = att' ∧ root = root' ∧ len = len' ∧ index = index') := by
  simp [Fact.chunk]
theorem Fact.chunk.inj {c : Id} {att : Id} {root : Id} {len : Nat} {index : Nat} {c' : Id} {att' : Id} {root' : Id} {len' : Nat} {index' : Nat}
    (hinj : Fact.chunk c att root len index = Fact.chunk c' att' root' len' index') : c = c' ∧ att = att' ∧ root = root' ∧ len = len' ∧ index = index' := by
  rw [Fact.chunk.injEq] at hinj; exact hinj
theorem Fact.endpoint.injEq (pk : ByteArray) (sk : ByteArray) (pk' : ByteArray) (sk' : ByteArray) :
    (Fact.endpoint pk sk = Fact.endpoint pk' sk') = (pk = pk' ∧ sk = sk') := by
  simp [Fact.endpoint]
theorem Fact.endpoint.inj {pk : ByteArray} {sk : ByteArray} {pk' : ByteArray} {sk' : ByteArray}
    (hinj : Fact.endpoint pk sk = Fact.endpoint pk' sk') : pk = pk' ∧ sk = sk' := by
  rw [Fact.endpoint.injEq] at hinj; exact hinj
theorem Fact.received.injEq (c : Id) (kid : Id) (msg : Id) (k : Nat) (clump : Option Id) (c' : Id) (kid' : Id) (msg' : Id) (k' : Nat) (clump' : Option Id) :
    (Fact.received c kid msg k clump = Fact.received c' kid' msg' k' clump') = (c = c' ∧ kid = kid' ∧ msg = msg' ∧ k = k' ∧ clump = clump') := by
  simp [Fact.received]
theorem Fact.received.inj {c : Id} {kid : Id} {msg : Id} {k : Nat} {clump : Option Id} {c' : Id} {kid' : Id} {msg' : Id} {k' : Nat} {clump' : Option Id}
    (hinj : Fact.received c kid msg k clump = Fact.received c' kid' msg' k' clump') : c = c' ∧ kid = kid' ∧ msg = msg' ∧ k = k' ∧ clump = clump' := by
  rw [Fact.received.injEq] at hinj; exact hinj
theorem Body.root.injEq (device : ByteArray) (enc : ByteArray) (sig : ByteArray) (device' : ByteArray) (enc' : ByteArray) (sig' : ByteArray) :
    (Body.root device enc sig = Body.root device' enc' sig') = (device = device' ∧ enc = enc' ∧ sig = sig') := by
  simp [Body.root]
theorem Body.root.inj {device : ByteArray} {enc : ByteArray} {sig : ByteArray} {device' : ByteArray} {enc' : ByteArray} {sig' : ByteArray}
    (h : Body.root device enc sig = Body.root device' enc' sig') : device = device' ∧ enc = enc' ∧ sig = sig' := by
  rw [Body.root.injEq] at h; exact h
theorem Body.invite.injEq (bearer : Key) (link : Bool) (sig : ByteArray) (bearer' : Key) (link' : Bool) (sig' : ByteArray) :
    (Body.invite bearer link sig = Body.invite bearer' link' sig') = (bearer = bearer' ∧ link = link' ∧ sig = sig') := by
  simp [Body.invite]
theorem Body.invite.inj {bearer : Key} {link : Bool} {sig : ByteArray} {bearer' : Key} {link' : Bool} {sig' : ByteArray}
    (h : Body.invite bearer link sig = Body.invite bearer' link' sig') : bearer = bearer' ∧ link = link' ∧ sig = sig' := by
  rw [Body.invite.injEq] at h; exact h
theorem Body.request.injEq (device : ByteArray) (enc : ByteArray) (consent : ByteArray) (bearerSig : ByteArray) (device' : ByteArray) (enc' : ByteArray) (consent' : ByteArray) (bearerSig' : ByteArray) :
    (Body.request device enc consent bearerSig = Body.request device' enc' consent' bearerSig') = (device = device' ∧ enc = enc' ∧ consent = consent' ∧ bearerSig = bearerSig') := by
  simp [Body.request]
theorem Body.request.inj {device : ByteArray} {enc : ByteArray} {consent : ByteArray} {bearerSig : ByteArray} {device' : ByteArray} {enc' : ByteArray} {consent' : ByteArray} {bearerSig' : ByteArray}
    (h : Body.request device enc consent bearerSig = Body.request device' enc' consent' bearerSig') : device = device' ∧ enc = enc' ∧ consent = consent' ∧ bearerSig = bearerSig' := by
  rw [Body.request.injEq] at h; exact h
theorem Body.grant.injEq (sig : ByteArray) (sig' : ByteArray) :
    (Body.grant sig = Body.grant sig') = (sig = sig') := by
  simp [Body.grant]
theorem Body.grant.inj {sig : ByteArray} {sig' : ByteArray}
    (h : Body.grant sig = Body.grant sig') : sig = sig' := by
  rw [Body.grant.injEq] at h; exact h
theorem Body.remove.injEq (sig : ByteArray) (sig' : ByteArray) :
    (Body.remove sig = Body.remove sig') = (sig = sig') := by
  simp [Body.remove]
theorem Body.remove.inj {sig : ByteArray} {sig' : ByteArray}
    (h : Body.remove sig = Body.remove sig') : sig = sig' := by
  rw [Body.remove.injEq] at h; exact h
theorem Body.post.injEq (ckey : ByteArray) (text : ByteArray) (n : Nat) (time : Nat) (sig : ByteArray) (ckey' : ByteArray) (text' : ByteArray) (n' : Nat) (time' : Nat) (sig' : ByteArray) :
    (Body.post ckey text n time sig = Body.post ckey' text' n' time' sig') = (ckey = ckey' ∧ text = text' ∧ n = n' ∧ time = time' ∧ sig = sig') := by
  simp [Body.post]
theorem Body.post.inj {ckey : ByteArray} {text : ByteArray} {n : Nat} {time : Nat} {sig : ByteArray} {ckey' : ByteArray} {text' : ByteArray} {n' : Nat} {time' : Nat} {sig' : ByteArray}
    (h : Body.post ckey text n time sig = Body.post ckey' text' n' time' sig') : ckey = ckey' ∧ text = text' ∧ n = n' ∧ time = time' ∧ sig = sig' := by
  rw [Body.post.injEq] at h; exact h
theorem Body.wrap.injEq (ckey : ByteArray) (recipient : ByteArray) (box : ByteArray) (ckey' : ByteArray) (recipient' : ByteArray) (box' : ByteArray) :
    (Body.wrap ckey recipient box = Body.wrap ckey' recipient' box') = (ckey = ckey' ∧ recipient = recipient' ∧ box = box') := by
  simp [Body.wrap]
theorem Body.wrap.inj {ckey : ByteArray} {recipient : ByteArray} {box : ByteArray} {ckey' : ByteArray} {recipient' : ByteArray} {box' : ByteArray}
    (h : Body.wrap ckey recipient box = Body.wrap ckey' recipient' box') : ckey = ckey' ∧ recipient = recipient' ∧ box = box' := by
  rw [Body.wrap.injEq] at h; exact h
theorem Body.profile.injEq (name : ByteArray) (time : Nat) (sig : ByteArray) (name' : ByteArray) (time' : Nat) (sig' : ByteArray) :
    (Body.profile name time sig = Body.profile name' time' sig') = (name = name' ∧ time = time' ∧ sig = sig') := by
  simp [Body.profile]
theorem Body.profile.inj {name : ByteArray} {time : Nat} {sig : ByteArray} {name' : ByteArray} {time' : Nat} {sig' : ByteArray}
    (h : Body.profile name time sig = Body.profile name' time' sig') : name = name' ∧ time = time' ∧ sig = sig' := by
  rw [Body.profile.injEq] at h; exact h
theorem Body.attach.injEq (root : ByteArray) (len : Nat) (time : Nat) (kid : ByteArray) (sealed : ByteArray) (sig : ByteArray) (root' : ByteArray) (len' : Nat) (time' : Nat) (kid' : ByteArray) (sealed' : ByteArray) (sig' : ByteArray) :
    (Body.attach root len time kid sealed sig = Body.attach root' len' time' kid' sealed' sig') = (root = root' ∧ len = len' ∧ time = time' ∧ kid = kid' ∧ sealed = sealed' ∧ sig = sig') := by
  simp [Body.attach]
theorem Body.attach.inj {root : ByteArray} {len : Nat} {time : Nat} {kid : ByteArray} {sealed : ByteArray} {sig : ByteArray} {root' : ByteArray} {len' : Nat} {time' : Nat} {kid' : ByteArray} {sealed' : ByteArray} {sig' : ByteArray}
    (h : Body.attach root len time kid sealed sig = Body.attach root' len' time' kid' sealed' sig') : root = root' ∧ len = len' ∧ time = time' ∧ kid = kid' ∧ sealed = sealed' ∧ sig = sig' := by
  rw [Body.attach.injEq] at h; exact h
theorem Body.react.injEq (emoji : ByteArray) (time : Nat) (sig : ByteArray) (emoji' : ByteArray) (time' : Nat) (sig' : ByteArray) :
    (Body.react emoji time sig = Body.react emoji' time' sig') = (emoji = emoji' ∧ time = time' ∧ sig = sig') := by
  simp [Body.react]
theorem Body.react.inj {emoji : ByteArray} {time : Nat} {sig : ByteArray} {emoji' : ByteArray} {time' : Nat} {sig' : ByteArray}
    (h : Body.react emoji time sig = Body.react emoji' time' sig') : emoji = emoji' ∧ time = time' ∧ sig = sig' := by
  rw [Body.react.injEq] at h; exact h
theorem Body.approve.injEq (sig : ByteArray) (sig' : ByteArray) :
    (Body.approve sig = Body.approve sig') = (sig = sig') := by
  simp [Body.approve]
theorem Body.approve.inj {sig : ByteArray} {sig' : ByteArray}
    (h : Body.approve sig = Body.approve sig') : sig = sig' := by
  rw [Body.approve.injEq] at h; exact h
theorem Body.accept.injEq (c : Id) (device : Key) (c' : Id) (device' : Key) :
    (Body.accept c device = Body.accept c' device') = (c = c' ∧ device = device') := by
  simp [Body.accept]
theorem Body.accept.inj {c : Id} {device : Key} {c' : Id} {device' : Key}
    (h : Body.accept c device = Body.accept c' device') : c = c' ∧ device = device' := by
  rw [Body.accept.injEq] at h; exact h
theorem Body.joining.injEq (c : Id) (inviter : Key) (hints : List ByteArray) (req : Id) (name : ByteArray) (device : Key) (epoch : Nat) (c' : Id) (inviter' : Key) (hints' : List ByteArray) (req' : Id) (name' : ByteArray) (device' : Key) (epoch' : Nat) :
    (Body.joining c inviter hints req name device epoch = Body.joining c' inviter' hints' req' name' device' epoch') = (c = c' ∧ inviter = inviter' ∧ hints = hints' ∧ req = req' ∧ name = name' ∧ device = device' ∧ epoch = epoch') := by
  simp [Body.joining]
theorem Body.joining.inj {c : Id} {inviter : Key} {hints : List ByteArray} {req : Id} {name : ByteArray} {device : Key} {epoch : Nat} {c' : Id} {inviter' : Key} {hints' : List ByteArray} {req' : Id} {name' : ByteArray} {device' : Key} {epoch' : Nat}
    (h : Body.joining c inviter hints req name device epoch = Body.joining c' inviter' hints' req' name' device' epoch') : c = c' ∧ inviter = inviter' ∧ hints = hints' ∧ req = req' ∧ name = name' ∧ device = device' ∧ epoch = epoch' := by
  rw [Body.joining.injEq] at h; exact h
theorem Body.secret.injEq (pk : ByteArray) (seed : ByteArray) (pk' : ByteArray) (seed' : ByteArray) :
    (Body.secret pk seed = Body.secret pk' seed') = (pk = pk' ∧ seed = seed') := by
  simp [Body.secret]
theorem Body.secret.inj {pk : ByteArray} {seed : ByteArray} {pk' : ByteArray} {seed' : ByteArray}
    (h : Body.secret pk seed = Body.secret pk' seed') : pk = pk' ∧ seed = seed' := by
  rw [Body.secret.injEq] at h; exact h
theorem Body.name.injEq (n : Nat) (name : ByteArray) (sig : ByteArray) (n' : Nat) (name' : ByteArray) (sig' : ByteArray) :
    (Body.name n name sig = Body.name n' name' sig') = (n = n' ∧ name = name' ∧ sig = sig') := by
  simp [Body.name]
theorem Body.name.inj {n : Nat} {name : ByteArray} {sig : ByteArray} {n' : Nat} {name' : ByteArray} {sig' : ByteArray}
    (h : Body.name n name sig = Body.name n' name' sig') : n = n' ∧ name = name' ∧ sig = sig' := by
  rw [Body.name.injEq] at h; exact h
theorem Body.key.injEq (c : ByteArray) (k : ByteArray) (c' : ByteArray) (k' : ByteArray) :
    (Body.key c k = Body.key c' k') = (c = c' ∧ k = k') := by
  simp [Body.key]
theorem Body.key.inj {c : ByteArray} {k : ByteArray} {c' : ByteArray} {k' : ByteArray}
    (h : Body.key c k = Body.key c' k') : c = c' ∧ k = k' := by
  rw [Body.key.injEq] at h; exact h
theorem Body.chunk.injEq (root : ByteArray) (len : Nat) (time : Nat) (index : Nat) (slice : ByteArray) (sibs : List ByteArray) (root' : ByteArray) (len' : Nat) (time' : Nat) (index' : Nat) (slice' : ByteArray) (sibs' : List ByteArray) :
    (Body.chunk root len time index slice sibs = Body.chunk root' len' time' index' slice' sibs') = (root = root' ∧ len = len' ∧ time = time' ∧ index = index' ∧ slice = slice' ∧ sibs = sibs') := by
  simp [Body.chunk]
theorem Body.chunk.inj {root : ByteArray} {len : Nat} {time : Nat} {index : Nat} {slice : ByteArray} {sibs : List ByteArray} {root' : ByteArray} {len' : Nat} {time' : Nat} {index' : Nat} {slice' : ByteArray} {sibs' : List ByteArray}
    (h : Body.chunk root len time index slice sibs = Body.chunk root' len' time' index' slice' sibs') : root = root' ∧ len = len' ∧ time = time' ∧ index = index' ∧ slice = slice' ∧ sibs = sibs' := by
  rw [Body.chunk.injEq] at h; exact h
theorem Body.endpoint.injEq (sk : ByteArray) (sk' : ByteArray) :
    (Body.endpoint sk = Body.endpoint sk') = (sk = sk') := by
  simp [Body.endpoint]
theorem Body.endpoint.inj {sk : ByteArray} {sk' : ByteArray}
    (h : Body.endpoint sk = Body.endpoint sk') : sk = sk' := by
  rw [Body.endpoint.injEq] at h; exact h
theorem Body.receive.injEq (k : Nat) (k' : Nat) :
    (Body.receive k = Body.receive k') = (k = k') := by
  simp [Body.receive]
theorem Body.receive.inj {k : Nat} {k' : Nat}
    (h : Body.receive k = Body.receive k') : k = k' := by
  rw [Body.receive.injEq] at h; exact h

/-- Each op type's fact, if a fact is one. -/
@[simp] def Fact.admission? : Fact → Option Root.Fact
  | .ofAdmission x => some x
  | _ => none
@[simp] def Fact.invitation? : Fact → Option Invitation.Fact
  | .ofInvitation x => some x
  | _ => none
@[simp] def Fact.admin? : Fact → Option Grant.Fact
  | .ofAdmin x => some x
  | _ => none
@[simp] def Fact.removal? : Fact → Option Remove.Fact
  | .ofRemoval x => some x
  | _ => none
@[simp] def Fact.message? : Fact → Option Post.Fact
  | .ofMessage x => some x
  | _ => none
@[simp] def Fact.wrap? : Fact → Option Wrap.Fact
  | .ofWrap x => some x
  | _ => none
@[simp] def Fact.profile? : Fact → Option Profile.Fact
  | .ofProfile x => some x
  | _ => none
@[simp] def Fact.attachment? : Fact → Option Attach.Fact
  | .ofAttachment x => some x
  | _ => none
@[simp] def Fact.react? : Fact → Option React.Fact
  | .ofReact x => some x
  | _ => none
@[simp] def Fact.request? : Fact → Option Request.Fact
  | .ofRequest x => some x
  | _ => none
@[simp] def Fact.approval? : Fact → Option Approve.Fact
  | .ofApproval x => some x
  | _ => none
@[simp] def Fact.secret? : Fact → Option Secret.Fact
  | .ofSecret x => some x
  | _ => none
@[simp] def Fact.accepted? : Fact → Option Accept.Fact
  | .ofAccepted x => some x
  | _ => none
@[simp] def Fact.joining? : Fact → Option Joining.Fact
  | .ofJoining x => some x
  | _ => none
@[simp] def Fact.named? : Fact → Option Rename.Fact
  | .ofNamed x => some x
  | _ => none
@[simp] def Fact.abandoned? : Fact → Option Abandon.Fact
  | .ofAbandoned x => some x
  | _ => none
@[simp] def Fact.key? : Fact → Option ContentKey.Fact
  | .ofKey x => some x
  | _ => none
@[simp] def Fact.chunk? : Fact → Option Chunk.Fact
  | .ofChunk x => some x
  | _ => none
@[simp] def Fact.endpoint? : Fact → Option Endpoint.Fact
  | .ofEndpoint x => some x
  | _ => none
@[simp] def Fact.received? : Fact → Option Receive.Fact
  | .ofReceived x => some x
  | _ => none
@[simp] def Fact.draft? : Fact → Option Draft.Fact
  | .ofDraft x => some x
  | _ => none

/-! ## Bytes: each op type writes its own, tag first -/

/-- Bytes read as one op type's body or fact, then lifted into the family. -/
def decWith {α β} [Codec α] (f : α → β) (bs : List UInt8) : Option (β × List UInt8) :=
  (Codec.dec bs : Option (α × List UInt8)).map fun p => (f p.1, p.2)

def Body.enc : Body → List UInt8
  | .ofRoot a => Codec.enc a
  | .ofInvite a => Codec.enc a
  | .ofRequest a => Codec.enc a
  | .ofGrant a => Codec.enc a
  | .ofRemove a => Codec.enc a
  | .ofPost a => Codec.enc a
  | .ofWrap a => Codec.enc a
  | .ofProfile a => Codec.enc a
  | .ofAttach a => Codec.enc a
  | .ofReact a => Codec.enc a
  | .ofApprove a => Codec.enc a
  | .ofAdmit a => Codec.enc a
  | .ofAccept a => Codec.enc a
  | .ofJoining a => Codec.enc a
  | .ofSecret a => Codec.enc a
  | .ofName a => Codec.enc a
  | .ofAbandon a => Codec.enc a
  | .ofKey a => Codec.enc a
  | .ofChunk a => Codec.enc a
  | .ofEndpoint a => Codec.enc a
  | .ofReceive a => Codec.enc a
  | .ofDraft a => Codec.enc a

def Body.dec (bs : List UInt8) : Option (Body × List UInt8) :=
  match bs.head? with
  | some 0 => decWith Body.ofRoot bs
  | some 1 => decWith Body.ofInvite bs
  | some 12 => decWith Body.ofRequest bs
  | some 3 => decWith Body.ofGrant bs
  | some 4 => decWith Body.ofRemove bs
  | some 23 => decWith Body.ofPost bs
  | some 6 => decWith Body.ofWrap bs
  | some 7 => decWith Body.ofProfile bs
  | some 8 => decWith Body.ofAttach bs
  | some 9 => decWith Body.ofReact bs
  | some 10 => decWith Body.ofApprove bs
  | some 11 => decWith Body.ofAdmit bs
  | some 13 => decWith Body.ofAccept bs
  | some 14 => decWith Body.ofJoining bs
  | some 15 => decWith Body.ofSecret bs
  | some 16 => decWith Body.ofName bs
  | some 17 => decWith Body.ofAbandon bs
  | some 18 => decWith Body.ofKey bs
  | some 19 => decWith Body.ofChunk bs
  | some 22 => decWith Body.ofEndpoint bs
  | some 24 => decWith Body.ofReceive bs
  | some 25 => decWith Body.ofDraft bs
  | _ => none

def Body.encInto (buf : ByteArray) : Body → ByteArray
  | .ofRoot a => Codec.encInto buf a
  | .ofInvite a => Codec.encInto buf a
  | .ofRequest a => Codec.encInto buf a
  | .ofGrant a => Codec.encInto buf a
  | .ofRemove a => Codec.encInto buf a
  | .ofPost a => Codec.encInto buf a
  | .ofWrap a => Codec.encInto buf a
  | .ofProfile a => Codec.encInto buf a
  | .ofAttach a => Codec.encInto buf a
  | .ofReact a => Codec.encInto buf a
  | .ofApprove a => Codec.encInto buf a
  | .ofAdmit a => Codec.encInto buf a
  | .ofAccept a => Codec.encInto buf a
  | .ofJoining a => Codec.encInto buf a
  | .ofSecret a => Codec.encInto buf a
  | .ofName a => Codec.encInto buf a
  | .ofAbandon a => Codec.encInto buf a
  | .ofKey a => Codec.encInto buf a
  | .ofChunk a => Codec.encInto buf a
  | .ofEndpoint a => Codec.encInto buf a
  | .ofReceive a => Codec.encInto buf a
  | .ofDraft a => Codec.encInto buf a

def Body.decFrom (b : ByteArray) (i : Nat) : Option (Body × Nat) :=
  match b[i]? with
  | some 0 => decFromAs Body.ofRoot b i
  | some 1 => decFromAs Body.ofInvite b i
  | some 12 => decFromAs Body.ofRequest b i
  | some 3 => decFromAs Body.ofGrant b i
  | some 4 => decFromAs Body.ofRemove b i
  | some 23 => decFromAs Body.ofPost b i
  | some 6 => decFromAs Body.ofWrap b i
  | some 7 => decFromAs Body.ofProfile b i
  | some 8 => decFromAs Body.ofAttach b i
  | some 9 => decFromAs Body.ofReact b i
  | some 10 => decFromAs Body.ofApprove b i
  | some 11 => decFromAs Body.ofAdmit b i
  | some 13 => decFromAs Body.ofAccept b i
  | some 14 => decFromAs Body.ofJoining b i
  | some 15 => decFromAs Body.ofSecret b i
  | some 16 => decFromAs Body.ofName b i
  | some 17 => decFromAs Body.ofAbandon b i
  | some 18 => decFromAs Body.ofKey b i
  | some 19 => decFromAs Body.ofChunk b i
  | some 22 => decFromAs Body.ofEndpoint b i
  | some 24 => decFromAs Body.ofReceive b i
  | some 25 => decFromAs Body.ofDraft b i
  | _ => none

theorem Body.dec_of {α} [Codec α] {t : UInt8} (f : α → Body) (a : α) (rest : List UInt8)
    (ht : (Codec.enc a).head? = some t) (hd : ∀ bs : List UInt8, bs.head? = some t → Body.dec bs = decWith f bs) :
    Body.dec (Codec.enc a ++ rest) = some (f a, rest) := by
  have h1 : (Codec.enc a ++ rest).head? = some t := by
    cases h : Codec.enc a with
    | nil => simp [h] at ht
    | cons x l => simpa [h] using ht
  rw [hd _ h1]; simp [decWith, Codec.round]

theorem Body.decFrom_of {α} [Codec α] {t : UInt8} (f : α → Body) (a : α) {b : ByteArray} {i : Nat}
    (ht : (Codec.enc a).head? = some t) (hd : ∀ (b : ByteArray) (i : Nat), b[i]? = some t → Body.decFrom b i = decFromAs f b i)
    (h : Codec.At b i (Codec.enc a)) : Body.decFrom b i = some (f a, i + (Codec.enc a).length) := by
  have hb : b[i]? = some t := by
    cases he : Codec.enc a with
    | nil => simp [he] at ht
    | cons x l =>
      simp [he] at ht; subst ht; rw [he] at h; exact h.tag
  rw [hd b i hb]; exact decFromAs_at f h

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round x rest := by
    cases x with
    | ofRoot a => exact Body.dec_of (t := 0) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofInvite a => exact Body.dec_of (t := 1) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofRequest a => exact Body.dec_of (t := 12) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofGrant a => exact Body.dec_of (t := 3) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofRemove a => exact Body.dec_of (t := 4) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofPost a => exact Body.dec_of (t := 23) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofWrap a => exact Body.dec_of (t := 6) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofProfile a => exact Body.dec_of (t := 7) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofAttach a => exact Body.dec_of (t := 8) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofReact a => exact Body.dec_of (t := 9) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofApprove a => exact Body.dec_of (t := 10) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofAdmit a => exact Body.dec_of (t := 11) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofAccept a => exact Body.dec_of (t := 13) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofJoining a => exact Body.dec_of (t := 14) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofSecret a => exact Body.dec_of (t := 15) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofName a => exact Body.dec_of (t := 16) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofAbandon a => exact Body.dec_of (t := 17) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofKey a => exact Body.dec_of (t := 18) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofChunk a => exact Body.dec_of (t := 19) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofEndpoint a => exact Body.dec_of (t := 22) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofReceive a => exact Body.dec_of (t := 24) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofDraft a => exact Body.dec_of (t := 25) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
  encInto := Body.encInto
  encInto_eq buf x := by cases x <;> exact Codec.encInto_eq _ _
  decFrom := Body.decFrom
  decFrom_at x h := by
    cases x with
    | ofRoot a => exact Body.decFrom_of (t := 0) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofInvite a => exact Body.decFrom_of (t := 1) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofRequest a => exact Body.decFrom_of (t := 12) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofGrant a => exact Body.decFrom_of (t := 3) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofRemove a => exact Body.decFrom_of (t := 4) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofPost a => exact Body.decFrom_of (t := 23) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofWrap a => exact Body.decFrom_of (t := 6) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofProfile a => exact Body.decFrom_of (t := 7) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofAttach a => exact Body.decFrom_of (t := 8) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofReact a => exact Body.decFrom_of (t := 9) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofApprove a => exact Body.decFrom_of (t := 10) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofAdmit a => exact Body.decFrom_of (t := 11) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofAccept a => exact Body.decFrom_of (t := 13) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofJoining a => exact Body.decFrom_of (t := 14) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofSecret a => exact Body.decFrom_of (t := 15) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofName a => exact Body.decFrom_of (t := 16) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofAbandon a => exact Body.decFrom_of (t := 17) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofKey a => exact Body.decFrom_of (t := 18) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofChunk a => exact Body.decFrom_of (t := 19) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofEndpoint a => exact Body.decFrom_of (t := 22) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofReceive a => exact Body.decFrom_of (t := 24) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofDraft a => exact Body.decFrom_of (t := 25) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h

def Fact.enc : Fact → List UInt8
  | .ofAdmission a => Codec.enc a
  | .ofInvitation a => Codec.enc a
  | .ofAdmin a => Codec.enc a
  | .ofRemoval a => Codec.enc a
  | .ofMessage a => Codec.enc a
  | .ofWrap a => Codec.enc a
  | .ofProfile a => Codec.enc a
  | .ofAttachment a => Codec.enc a
  | .ofReact a => Codec.enc a
  | .ofRequest a => Codec.enc a
  | .ofApproval a => Codec.enc a
  | .ofSecret a => Codec.enc a
  | .ofAccepted a => Codec.enc a
  | .ofJoining a => Codec.enc a
  | .ofNamed a => Codec.enc a
  | .ofAbandoned a => Codec.enc a
  | .ofKey a => Codec.enc a
  | .ofChunk a => Codec.enc a
  | .ofEndpoint a => Codec.enc a
  | .ofReceived a => Codec.enc a
  | .ofDraft a => Codec.enc a

def Fact.dec (bs : List UInt8) : Option (Fact × List UInt8) :=
  match bs.head? with
  | some 0 => decWith Fact.ofAdmission bs
  | some 1 => decWith Fact.ofInvitation bs
  | some 2 => decWith Fact.ofAdmin bs
  | some 3 => decWith Fact.ofRemoval bs
  | some 21 => decWith Fact.ofMessage bs
  | some 23 => decWith Fact.ofMessage bs
  | some 5 => decWith Fact.ofWrap bs
  | some 6 => decWith Fact.ofProfile bs
  | some 7 => decWith Fact.ofAttachment bs
  | some 8 => decWith Fact.ofReact bs
  | some 9 => decWith Fact.ofRequest bs
  | some 10 => decWith Fact.ofApproval bs
  | some 11 => decWith Fact.ofSecret bs
  | some 12 => decWith Fact.ofAccepted bs
  | some 13 => decWith Fact.ofJoining bs
  | some 14 => decWith Fact.ofNamed bs
  | some 15 => decWith Fact.ofAbandoned bs
  | some 16 => decWith Fact.ofKey bs
  | some 17 => decWith Fact.ofChunk bs
  | some 20 => decWith Fact.ofEndpoint bs
  | some 22 => decWith Fact.ofReceived bs
  | some 24 => decWith Fact.ofReceived bs
  | some 25 => decWith Fact.ofDraft bs
  | _ => none

def Fact.encInto (buf : ByteArray) : Fact → ByteArray
  | .ofAdmission a => Codec.encInto buf a
  | .ofInvitation a => Codec.encInto buf a
  | .ofAdmin a => Codec.encInto buf a
  | .ofRemoval a => Codec.encInto buf a
  | .ofMessage a => Codec.encInto buf a
  | .ofWrap a => Codec.encInto buf a
  | .ofProfile a => Codec.encInto buf a
  | .ofAttachment a => Codec.encInto buf a
  | .ofReact a => Codec.encInto buf a
  | .ofRequest a => Codec.encInto buf a
  | .ofApproval a => Codec.encInto buf a
  | .ofSecret a => Codec.encInto buf a
  | .ofAccepted a => Codec.encInto buf a
  | .ofJoining a => Codec.encInto buf a
  | .ofNamed a => Codec.encInto buf a
  | .ofAbandoned a => Codec.encInto buf a
  | .ofKey a => Codec.encInto buf a
  | .ofChunk a => Codec.encInto buf a
  | .ofEndpoint a => Codec.encInto buf a
  | .ofReceived a => Codec.encInto buf a
  | .ofDraft a => Codec.encInto buf a

def Fact.decFrom (b : ByteArray) (i : Nat) : Option (Fact × Nat) :=
  match b[i]? with
  | some 0 => decFromAs Fact.ofAdmission b i
  | some 1 => decFromAs Fact.ofInvitation b i
  | some 2 => decFromAs Fact.ofAdmin b i
  | some 3 => decFromAs Fact.ofRemoval b i
  | some 21 => decFromAs Fact.ofMessage b i
  | some 23 => decFromAs Fact.ofMessage b i
  | some 5 => decFromAs Fact.ofWrap b i
  | some 6 => decFromAs Fact.ofProfile b i
  | some 7 => decFromAs Fact.ofAttachment b i
  | some 8 => decFromAs Fact.ofReact b i
  | some 9 => decFromAs Fact.ofRequest b i
  | some 10 => decFromAs Fact.ofApproval b i
  | some 11 => decFromAs Fact.ofSecret b i
  | some 12 => decFromAs Fact.ofAccepted b i
  | some 13 => decFromAs Fact.ofJoining b i
  | some 14 => decFromAs Fact.ofNamed b i
  | some 15 => decFromAs Fact.ofAbandoned b i
  | some 16 => decFromAs Fact.ofKey b i
  | some 17 => decFromAs Fact.ofChunk b i
  | some 20 => decFromAs Fact.ofEndpoint b i
  | some 22 => decFromAs Fact.ofReceived b i
  | some 24 => decFromAs Fact.ofReceived b i
  | some 25 => decFromAs Fact.ofDraft b i
  | _ => none

theorem Fact.dec_of {α} [Codec α] {t : UInt8} (f : α → Fact) (a : α) (rest : List UInt8)
    (ht : (Codec.enc a).head? = some t) (hd : ∀ bs : List UInt8, bs.head? = some t → Fact.dec bs = decWith f bs) :
    Fact.dec (Codec.enc a ++ rest) = some (f a, rest) := by
  have h1 : (Codec.enc a ++ rest).head? = some t := by
    cases h : Codec.enc a with
    | nil => simp [h] at ht
    | cons x l => simpa [h] using ht
  rw [hd _ h1]; simp [decWith, Codec.round]

theorem Fact.decFrom_of {α} [Codec α] {t : UInt8} (f : α → Fact) (a : α) {b : ByteArray} {i : Nat}
    (ht : (Codec.enc a).head? = some t) (hd : ∀ (b : ByteArray) (i : Nat), b[i]? = some t → Fact.decFrom b i = decFromAs f b i)
    (h : Codec.At b i (Codec.enc a)) : Fact.decFrom b i = some (f a, i + (Codec.enc a).length) := by
  have hb : b[i]? = some t := by
    cases he : Codec.enc a with
    | nil => simp [he] at ht
    | cons x l =>
      simp [he] at ht; subst ht; rw [he] at h; exact h.tag
  rw [hd b i hb]; exact decFromAs_at f h

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round x rest := by
    cases x with
    | ofAdmission a => exact Fact.dec_of (t := 0) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofInvitation a => exact Fact.dec_of (t := 1) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofAdmin a => exact Fact.dec_of (t := 2) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofRemoval a => exact Fact.dec_of (t := 3) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofMessage a =>
      rcases a with ⟨c, u, device, ckey, text, n, time, _ | root⟩
      · exact Fact.dec_of (t := 21) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
      · exact Fact.dec_of (t := 23) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofWrap a => exact Fact.dec_of (t := 5) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofProfile a => exact Fact.dec_of (t := 6) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofAttachment a => exact Fact.dec_of (t := 7) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofReact a => exact Fact.dec_of (t := 8) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofRequest a => exact Fact.dec_of (t := 9) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofApproval a => exact Fact.dec_of (t := 10) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofSecret a => exact Fact.dec_of (t := 11) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofAccepted a => exact Fact.dec_of (t := 12) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofJoining a => exact Fact.dec_of (t := 13) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofNamed a => exact Fact.dec_of (t := 14) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofAbandoned a => exact Fact.dec_of (t := 15) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofKey a => exact Fact.dec_of (t := 16) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofChunk a => exact Fact.dec_of (t := 17) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofEndpoint a => exact Fact.dec_of (t := 20) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofReceived a =>
      rcases a with ⟨c, kid, msg, k, _ | root⟩
      · exact Fact.dec_of (t := 22) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
      · exact Fact.dec_of (t := 24) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofDraft a => exact Fact.dec_of (t := 25) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
  encInto := Fact.encInto
  encInto_eq buf x := by cases x <;> exact Codec.encInto_eq _ _
  decFrom := Fact.decFrom
  decFrom_at x h := by
    cases x with
    | ofAdmission a => exact Fact.decFrom_of (t := 0) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofInvitation a => exact Fact.decFrom_of (t := 1) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofAdmin a => exact Fact.decFrom_of (t := 2) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofRemoval a => exact Fact.decFrom_of (t := 3) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofMessage a =>
      rcases a with ⟨c, u, device, ckey, text, n, time, _ | root⟩
      · exact Fact.decFrom_of (t := 21) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
      · exact Fact.decFrom_of (t := 23) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofWrap a => exact Fact.decFrom_of (t := 5) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofProfile a => exact Fact.decFrom_of (t := 6) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofAttachment a => exact Fact.decFrom_of (t := 7) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofReact a => exact Fact.decFrom_of (t := 8) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofRequest a => exact Fact.decFrom_of (t := 9) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofApproval a => exact Fact.decFrom_of (t := 10) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofSecret a => exact Fact.decFrom_of (t := 11) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofAccepted a => exact Fact.decFrom_of (t := 12) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofJoining a => exact Fact.decFrom_of (t := 13) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofNamed a => exact Fact.decFrom_of (t := 14) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofAbandoned a => exact Fact.decFrom_of (t := 15) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofKey a => exact Fact.decFrom_of (t := 16) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofChunk a => exact Fact.decFrom_of (t := 17) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofEndpoint a => exact Fact.decFrom_of (t := 20) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofReceived a =>
      rcases a with ⟨c, kid, msg, k, _ | root⟩
      · exact Fact.decFrom_of (t := 22) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
      · exact Fact.decFrom_of (t := 24) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofDraft a => exact Fact.decFrom_of (t := 25) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h

/-! ## Signing -/

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned : Body → Body
  | .ofRoot b => .ofRoot b.unsigned
  | .ofInvite b => .ofInvite b.unsigned
  | .ofRequest b => .ofRequest b.unsigned
  | .ofGrant b => .ofGrant b.unsigned
  | .ofRemove b => .ofRemove b.unsigned
  | .ofPost b => .ofPost b.unsigned
  | .ofWrap b => .ofWrap b.unsigned
  | .ofProfile b => .ofProfile b.unsigned
  | .ofAttach b => .ofAttach b.unsigned
  | .ofReact b => .ofReact b.unsigned
  | .ofApprove b => .ofApprove b.unsigned
  | .ofAdmit b => .ofAdmit b.unsigned
  | .ofAccept b => .ofAccept b.unsigned
  | .ofJoining b => .ofJoining b.unsigned
  | .ofSecret b => .ofSecret b.unsigned
  | .ofName b => .ofName b.unsigned
  | .ofAbandon b => .ofAbandon b.unsigned
  | .ofKey b => .ofKey b.unsigned
  | .ofChunk b => .ofChunk b.unsigned
  | .ofEndpoint b => .ofEndpoint b.unsigned
  | .ofReceive b => .ofReceive b.unsigned
  | .ofDraft b => .ofDraft b.unsigned

/-- The bytes a signature on an op covers: its op type's (`signedBy`). -/
def signed (o : Op) (b : Body) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, o.reqs, b.unsigned)


/-- What an op type's validator checks a signature over is the family's `signed`. -/
@[simp] theorem signedBy_ofRoot (o : Op) (b : Root.Body) : signedBy o b.unsigned = signed o (.ofRoot b) := rfl
@[simp] theorem signedBy_ofInvite (o : Op) (b : Invitation.Body) : signedBy o b.unsigned = signed o (.ofInvite b) := rfl
@[simp] theorem signedBy_ofRequest (o : Op) (b : Request.Body) : signedBy o b.unsigned = signed o (.ofRequest b) := rfl
@[simp] theorem signedBy_ofGrant (o : Op) (b : Grant.Body) : signedBy o b.unsigned = signed o (.ofGrant b) := rfl
@[simp] theorem signedBy_ofRemove (o : Op) (b : Remove.Body) : signedBy o b.unsigned = signed o (.ofRemove b) := rfl
@[simp] theorem signedBy_ofPost (o : Op) (b : Post.Body) : signedBy o b.unsigned = signed o (.ofPost b) := rfl
@[simp] theorem signedBy_ofProfile (o : Op) (b : Profile.Body) : signedBy o b.unsigned = signed o (.ofProfile b) := rfl
@[simp] theorem signedBy_ofAttach (o : Op) (b : Attach.Body) : signedBy o b.unsigned = signed o (.ofAttach b) := rfl
@[simp] theorem signedBy_ofReact (o : Op) (b : React.Body) : signedBy o b.unsigned = signed o (.ofReact b) := rfl
@[simp] theorem signedBy_ofApprove (o : Op) (b : Approve.Body) : signedBy o b.unsigned = signed o (.ofApprove b) := rfl
@[simp] theorem signedBy_ofName (o : Op) (b : Rename.Body) : signedBy o b.unsigned = signed o (.ofName b) := rfl

/-! ## Validity -/

/-- Whether a fact is this device's own: local ops' facts, never
shared, never read by a shared op's validator (`check_reads_shared`). -/
def Fact.isLocal : Fact → Bool
  | .ofSecret _ | .ofAccepted _ | .ofJoining _ | .ofAbandoned _ | .ofKey _ | .ofEndpoint _ | .ofReceived _ | .ofDraft _ => true
  | _ => false

/-- Whether a fact shows that user u of community c is admin: the
founder's admission (the founder's user is the community), or a grant. -/
def isAdmin (c u : Id) : Fact → Bool
  | .admission c' u' _ _ => decide (c' = c ∧ u' = c ∧ u = c)
  | .admin c' u' => decide (c' = c ∧ u' = u)
  | _ => false

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

/-- An op's validator, by its body, over the facts its requirements
produced (slot order): its op type's (each folder's Validate.lean), given
the facts it cites, typed. Slot 0 is the community's root, whose fact is
the founder's admission with the community's id. -/
def check (C : Crypto) (o : Op) : Body → List Fact → Option Fact
  | .ofRoot b, [] => (Root.check C o b).map .ofAdmission
  | .ofInvite b, [.ofAdmission r, .ofAdmission a] => (Invitation.check C o b r a).map .ofInvitation
  | .ofRequest b, [.ofAdmission r, .ofInvitation i] => (Request.check C o b r i).map .ofRequest
  | .ofApprove b, [.ofAdmission r, .ofRequest q, .ofAdmission a] => (Approve.check C o b r q a).map .ofApproval
  | .ofAdmit b, [.ofAdmission r, .ofRequest q, .ofApproval a] => (Admit.check o b r q a).map .ofAdmission
  | .ofGrant b, [.ofAdmission r, .ofAdmission a, auth, .ofAdmission t] =>
    (Grant.check C o b r a (isAdmin r.c a.u auth) t).map .ofAdmin
  | .ofRemove b, [.ofAdmission r, .ofAdmission a, auth, .ofAdmission t] =>
    (Remove.check C o b r a (decide (auth = .ofAdmission a) && decide (o.reqs[2]? = o.reqs[1]?))
      (isAdmin r.c a.u auth) t).map .ofRemoval
  | .ofPost b, [.ofAdmission r, .ofAdmission a] => (Post.check C o b r a none).map .ofMessage
  | .ofPost b, [.ofAdmission r, .ofAdmission a, .ofMessage p] => (Post.check C o b r a (some p)).map .ofMessage
  | .ofProfile b, [.ofAdmission r, .ofAdmission a] => (Profile.check C o b r a).map .ofProfile
  | .ofAttach b, [.ofAdmission r, .ofAdmission a, .ofMessage m] => (Attach.check C o b r a m).map .ofAttachment
  | .ofChunk b, [.ofAdmission r, .ofAttachment t] => (Chunk.check o b r t).map .ofChunk
  | .ofReact b, [.ofAdmission r, .ofAdmission a, .ofMessage m] => (React.check C o b r a m).map .ofReact
  | .ofWrap b, [.ofAdmission r] => (Wrap.check o b r).map .ofWrap
  | .ofSecret b, [] => (Secret.check C b).map .ofSecret
  | .ofKey b, [] => (ContentKey.check b).map .ofKey
  | .ofEndpoint b, [] => (Endpoint.check b).map .ofEndpoint
  | .ofAccept b, [] => (Accept.check b).map .ofAccepted
  | .ofJoining b, [] => (Joining.check b).map .ofJoining
  | .ofAbandon b, [.ofJoining j] => (Abandon.check o b j).map .ofAbandoned
  | .ofReceive b, [.ofMessage m] => (Receive.check o b m).map .ofReceived
  | .ofDraft b, [] => (Draft.check o b).map .ofDraft
  | .ofName b, .ofAdmission r :: .ofAdmission a :: auth :: prev =>
    (Rename.check C o b r a (isAdmin r.c a.u auth) (counterOk r.c b.n prev)).map .ofNamed
  | _, _ => none

/-- Each body's op type. -/
def Body.tag : Body → UInt8
  | .ofRoot _ => 0 | .ofInvite _ => 1 | .ofRequest _ => 12 | .ofGrant _ => 3
  | .ofRemove _ => 4 | .ofWrap _ => 6
  | .ofProfile _ => 7 | .ofAttach _ => 8 | .ofReact _ => 9
  | .ofApprove _ => 10 | .ofAdmit _ => 11
  | .ofAccept _ => 13 | .ofJoining _ => 14 | .ofSecret _ => 15 | .ofName _ => 16 | .ofAbandon _ => 17
  | .ofKey _ => 18 | .ofChunk _ => 19 | .ofEndpoint _ => 22 | .ofPost _ => 23 | .ofReceive _ => 24
  | .ofDraft _ => 25

/-- An op's verdict: its body's, if its type is its body's. The type is
in the bytes its id hashes, so an op re-sent under another type would be
another op with the same fact: a message shown twice, a chunk counted
twice (`op_of_valid`). -/
def validate (C : Crypto) (o : Op) (fs : List Fact) : Option Fact :=
  match (decode o.body : Option Body) with
  | none => none
  | some b => if o.kind = b.tag then check C o b fs else none

/-! ## Relations: each op type's lists, read in the family (same names, so the same keys) -/
namespace admission
def byDevice : Rel Fact := Root.byDevice.comap Fact.admission?
def all : Rel Fact := Root.all.comap Fact.admission?
def byUser : Rel Fact := Root.byUser.comap Fact.admission?
def byKey : Rel Fact := Root.byKey.comap Fact.admission?
end admission

namespace removal
def byUser : Rel Fact := Remove.byUser.comap Fact.removal?
end removal

namespace admin
def byUser : Rel Fact := Grant.byUser.comap Fact.admin?
end admin

namespace message
def all : Rel Fact := Post.all.comap Fact.message?
def byAuthor : Rel Fact := Post.byAuthor.comap Fact.message?
def byKey : Rel Fact := Post.byKey.comap Fact.message?
def rootsByKey : Rel Fact := Post.rootsByKey.comap Fact.message?
def childrenByKey : Rel Fact := Post.childrenByKey.comap Fact.message?
end message

namespace received
def byKey : Rel Fact := Receive.byKey.comap Fact.received?
def all : Rel Fact := Receive.all.comap Fact.received?
def byMsg : Rel Fact := Receive.byMsg.comap Fact.received?
def rootsByKey : Rel Fact := Receive.rootsByKey.comap Fact.received?
def childrenByKey : Rel Fact := Receive.childrenByKey.comap Fact.received?
end received

namespace draft
def byAcc : Rel Fact := Draft.byAcc.comap Fact.draft?
end draft

namespace wrap
def byContentKey : Rel Fact := Wrap.byContentKey.comap Fact.wrap?
def byRecipient : Rel Fact := Wrap.byRecipient.comap Fact.wrap?
end wrap

namespace key
def byCommunity : Rel Fact := ContentKey.byCommunity.comap Fact.key?
def byId : Rel Fact := ContentKey.byId.comap Fact.key?
end key

namespace profile
def byUser : Rel Fact := Profile.byUser.comap Fact.profile?
def all : Rel Fact := Profile.all.comap Fact.profile?
def byLook : Rel Fact := Profile.byLook.comap Fact.profile?
end profile

namespace react
def byMessage : Rel Fact := React.byMessage.comap Fact.react?
def byMessageEmoji : Rel Fact := React.byMessageEmoji.comap Fact.react?
end react

namespace request
def all : Rel Fact := Request.all.comap Fact.request?
end request

namespace approval
def byRequest : Rel Fact := Approve.byRequest.comap Fact.approval?
end approval

namespace secret
def byKey : Rel Fact := Secret.byKey.comap Fact.secret?
def all : Rel Fact := Secret.all.comap Fact.secret?
end secret

namespace endpoint
def all : Rel Fact := Endpoint.all.comap Fact.endpoint?
end endpoint

namespace accepted
def all : Rel Fact := Accept.all.comap Fact.accepted?
end accepted

namespace joining
def all : Rel Fact := Joining.all.comap Fact.joining?
end joining

namespace abandoned
def byRequest : Rel Fact := Abandon.byRequest.comap Fact.abandoned?
def byJoining : Rel Fact := Abandon.byJoining.comap Fact.abandoned?
end abandoned

namespace named
def current : Rel Fact := Rename.current.comap Fact.named?
end named

namespace attachment
def byMessage : Rel Fact := Attach.byMessage.comap Fact.attachment?
end attachment

namespace chunk
def byAttachment : Rel Fact := Chunk.byAttachment.comap Fact.chunk?
end chunk


/-- Every relation of the community's facts. Invitations are in none
(read by their own key). -/
def rels : List (Rel Fact) :=
  [admission.byDevice, admission.all, admission.byUser, admission.byKey, removal.byUser, admin.byUser, message.all, message.byAuthor,
   message.byKey, received.byKey, received.all, received.byMsg,
   wrap.byContentKey, profile.byUser, profile.all, profile.byLook, react.byMessage, react.byMessageEmoji,
   request.all, approval.byRequest, secret.byKey, secret.all, accepted.all, joining.all, named.current,
   abandoned.byRequest, abandoned.byJoining, wrap.byRecipient, key.byCommunity, key.byId, attachment.byMessage,
   chunk.byAttachment, endpoint.all, message.rootsByKey, message.childrenByKey, received.rootsByKey, received.childrenByKey, draft.byAcc]

/-- The keys a fact is filed under: its relations'. -/
def keys : Fact → List ByteArray := keysOf rels

/-- Where a fact sorts under its keys: its op type's (messages by
counter and time, receipts by arrival, other timed facts by time; ties
by id), or nowhere in particular. -/
def sortOf : Fact → ByteArray
  | .ofMessage f => Post.sortKey f
  | .ofReceived f => Receive.sortKey f
  | .ofDraft f => Draft.sortKey f
  | .ofProfile f => Profile.sortKey f
  | .ofChunk f => Chunk.sortKey f
  | .ofReact f => React.sortKey f
  | .ofNamed f => Rename.sortKey f
  | _ => .empty

instance : SortKey Fact := ⟨sortOf⟩

/-- Whether an op is local, from its body: a device's secrets, its
acceptances and its joins are, never sent or taken; everything else is
shared in its community. -/
def Body.isLocal : Body → Bool
  | .ofSecret _ | .ofAccept _ | .ofJoining _ | .ofAbandon _ | .ofKey _ | .ofEndpoint _ | .ofReceive _ | .ofDraft _ => true
  | _ => false

/-- The community an op is about: a root founds its own; every other op
names its community first. -/
def Body.community (b : Body) (o : Op) : Id :=
  match b with
  | .ofRoot _ => o.id
  | _ => o.reqs.headD o.id

/-- Whether an op is the app's working state, never stored: a draft. -/
def Body.isEphemeral : Body → Bool
  | .ofDraft _ => true
  | _ => false

/-- The app's working state is this device's own too. -/
theorem Body.local_of_ephemeral {b : Body} (h : b.isEphemeral = true) : b.isLocal = true := by
  cases b <;> simp_all [Body.isEphemeral, Body.isLocal]

/-- Where an op travels: in memory only (a draft), local, or shared in
its community. -/
def scopeOf (o : Op) : Scope :=
  match (decode o.body : Option Body) with
  | some b => if b.isEphemeral then .ephemeral else if b.isLocal then .local else .shared (b.community o)
  | none => .shared (o.reqs.headD o.id)

/-- An op's claimed time, which sync ranges are over: a post's, a
profile's or a reaction's, and an attachment's or a chunk's (its
message's, so a photo syncs with its message: `chunks_in_window`); 0 for
the rest (roots, invitations, admissions, removals, ...), which every
window includes. A post's
counter does not feed it: sync's windows are over every timed kind in a
room, and only time is common to them, in minutes that mean the same on
every device; a counter orders one channel's messages only, and one
claim can saturate it. -/
def orderOf (o : Op) : Nat :=
  match (decode o.body : Option Body) with
  | some (.ofPost b) => b.time
  | some (.ofProfile b) => b.time
  | some (.ofReact b) => b.time
  | some (.ofAttach b) => b.time
  | some (.ofChunk b) => b.time
  | _ => 0

def family (C : Crypto) : Family Fact :=
  { validate := validate C, keys, scope := scopeOf, order := orderOf }

end Community

/-! ## What the family's laws and intents stand on: what Valid means, the
root's facts, and helpers that name no op type -/

namespace Community
open Engine Codec

theorem all2_two {α β} {R : α → β → Prop} {l : List α} {a b : β} (h : All2 R l [a, b]) :
    ∃ x y, l = [x, y] ∧ R x a ∧ R y b := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4; exact ⟨_, _, rfl, h1, h3⟩

theorem all2_cons2 {α β} {R : α → β → Prop} {l : List α} {a b : β} {rest : List β}
    (h : All2 R l (a :: b :: rest)) :
    ∃ x y t, l = x :: y :: t ∧ R x a ∧ R y b ∧ All2 R t rest := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => exact ⟨_, _, _, rfl, h1, h3, h4⟩

theorem all2_four {α β} {R : α → β → Prop} {l : List α} {a b c d : β} (h : All2 R l [a, b, c, d]) :
    ∃ x y z w, l = [x, y, z, w] ∧ R x a ∧ R y b ∧ R z c ∧ R w d := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with
  | cons h5 h6 => cases h6 with | cons h7 h8 => cases h8; exact ⟨_, _, _, _, rfl, h1, h3, h5, h7⟩

theorem all2_three {α β} {R : α → β → Prop} {l : List α} {a b c : β} (h : All2 R l [a, b, c]) :
    ∃ x y z, l = [x, y, z] ∧ R x a ∧ R y b ∧ R z c := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with
  | cons h5 h6 => cases h6; exact ⟨_, _, _, rfl, h1, h3, h5⟩

theorem All2.comp {α β γ} {R : α → β → Prop} {S : β → γ → Prop} {l : List α} {m : List β}
    {n : List γ} (h1 : All2 R l m) (h2 : All2 S m n) : All2 (fun a c => ∃ b, R a b ∧ S b c) l n := by
  induction h1 generalizing n with
  | nil => cases h2; exact .nil
  | cons ha _ ih => cases h2 with | cons hb hr => exact .cons ⟨_, ha, hb⟩ (ih hr)
open Engine Codec
section
variable (C : Crypto) (ops : Id → Option Op)

/-- x is Valid with fact f. -/
def V (x : Id) (f : Fact) : Prop := Spec (family C) ops x (.valid f)

/-- Device d is admitted into user u of community c, with key e. -/
def Admitted (c u : Id) (d e : Key) : Prop := ∃ x, V C ops x (.admission c u d e)
end
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

theorem valid_inv {x : Id} {f : Fact} (h : V C ops x f) :
    ∃ o b fs, ops x = some o ∧ (decode o.body : Option Body) = some b ∧
      All2 (fun r g => V C ops r g) o.reqs fs ∧ check C o b fs = some f := by
  obtain ⟨o, fs, hx, hr, hv⟩ := spec_valid_inv h
  unfold family validate at hv; simp only at hv
  cases hb : (decode o.body : Option Body) with
  | none => rw [hb] at hv; simp at hv
  | some b =>
    rw [hb] at hv; simp only at hv
    split at hv
    · exact ⟨o, b, fs, hx, hb, hr, hv⟩
    · cases hv

/-- **A Valid op is the op its requirements and body make**: its type is
its body's type and its body bytes are its body's encoding. So nobody
makes a second op of a Valid fact by re-sending it under another type. -/
theorem op_of_valid {x : Id} {f : Fact} (h : V C ops x f) :
    ∃ o b, ops x = some o ∧ o = Op.make b.tag o.reqs (encode b) ∧
      (decode o.body : Option Body) = some b := by
  obtain ⟨o, fs, hx, _, hv⟩ := spec_valid_inv h
  unfold family validate at hv; simp only at hv
  cases hb : (decode o.body : Option Body) with
  | none => rw [hb] at hv; simp at hv
  | some b =>
    rw [hb] at hv; simp only at hv
    split at hv
    · rename_i hkd
      exact ⟨o, b, hx, Op.ext' hkd rfl (Codec.encode_decode hb).symm, hb⟩
    · cases hv

/-- The signatures an op's body carries, each over `signed o b`: the
request's two (its device's consent and the invitation bearer's), one
for every other signed op, none for unsigned ones. -/
def Body.sigs : Body → List ByteArray
  | .root _ _ s | .invite _ _ s | .grant s | .remove s | .post _ _ _ _ s
  | .profile _ _ s | .attach _ _ _ _ _ s | .react _ _ s | .approve s | .name _ _ s => [s]
  | .request _ _ c b => [c, b]
  | _ => []

/-- **Signatures are unforgeable, over the ones a store holds.** Every
signature that an op in `ops` carries, and that verifies under key pk,
was made by pk's holder: `Signed pk m` says the holder signed m.

This is Ed25519's unforgeability as a fact about one store: it fails only
if a forgery is in the store. It is not stated over every byte string.
Every message has some valid signature under every key (finding one is
infeasible, not impossible), so the unscoped form, `∀ pk m s, verify pk m
s → Signed pk m`, holds only of a `Signed` true of every message
(`unscoped_signs_all`), and the laws built on it would then say nothing
about who signed. tests/vacuity/Contracts.lean (`unforgeableScoped`) has a
store where this form holds of a `Signed` that is false of other
messages, under a scheme with a valid signature for every message. -/
def Unforgeable (C : Crypto) (ops : Id → Option Op) (Signed : Key → ByteArray → Prop) : Prop :=
  ∀ x o b pk s, ops x = some o → (decode o.body : Option Body) = some b → s ∈ b.sigs →
    C.verify pk (signed o b) s = true → Signed pk (signed o b)

/-- Ops are stored under their own ids (Engine.Inv.key). -/
def Keyed (ops : Id → Option Op) : Prop := ∀ x o, ops x = some o → o.id = x

/-- **Removal does not rewrite history.** Every Valid fact stays Valid
as ops arrive, removals included: a removed user's messages, admissions
and attributions remain. -/
theorem valid_stays {ops' : Id → Option Op} (he : Extends ops ops') {x : Id} {f : Fact}
    (h : V C ops x f) : V C ops' x f := spec_extends he h

/-- The facts only a device's own local ops produce. -/

theorem check_local {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {f : Fact}
    (h : check C o b fs = some f) (hl : f.isLocal = true) : b.isLocal = true := by
  unfold check at h
  split at h <;> (try (simp at h; done)) <;> first
    | rfl
    | (obtain ⟨f', -, rfl⟩ := Option.map_eq_some_iff.1 h; simp [Fact.isLocal] at hl)

/-- **A device's own state is its own.** In a node fed by its own writes
and by peers' jobs through `intake`, every op behind a Valid secret,
acceptance or pending join is one of its own writes. -/
theorem local_fact_mine {M : List Op} {s : DB Fact} (hf : Fed (family C) M s) {x : Id} {f : Fact}
    (hv : V C s.ops x f) (hl : f.isLocal = true) : ∃ o ∈ M, s.ops x = some o := by
  obtain ⟨o, b, fs, hx, hb, _, hc⟩ := valid_inv hv
  refine ⟨o, stored_local hf hx ?_, hx⟩
  show (family C).room o = none
  have hl' := check_local hc hl
  simp only [Family.room, family, scopeOf, hb]
  cases b.isEphemeral <;> simp [hl']
open Engine

/-- What an intent writes: ops. Everything is ops, file bytes included
(an attachment's chunks). -/
structure Write where
  ops : List Op
open Engine Codec

/-- The op with these requirements and body, named by its bytes' hash. -/
def mkOp (reqs : List Id) (b : Body) : Op := Op.make b.tag reqs (encode b)

/-- A device: its Ed25519 signing key pair. Its X25519 key is its
node's (`endpoint`), named in the root or request that admits it. -/
structure Device where
  pk : Key
  sk : ByteArray
  deriving Inhabited

/-- A device from a 32-byte seed (tests derive seeds from names). -/
def Device.ofSeed (seed : ByteArray) : Device :=
  let kp := edKeypair seed
  ⟨kp.extract 0 32, kp.extract 32 96⟩

/-- What a signer signs for an op with these requirements and body. -/
def toSign (reqs : List Id) (b : Body) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, reqs, b.unsigned)

def sig (sk : ByteArray) (reqs : List Id) (b : Body) : ByteArray := edSign sk (toSign reqs b)

/-- What a link carries: the community, the invitation it redeems, the
inviter's node key and dial hints, and the invitation's bearer seed; and
whether it is a device link (its invitation admits another device of the
issuer's user) or a member's. -/
structure Invite where
  community : Id
  invitation : Id
  inviter : Key
  hints : List ByteArray
  secret : ByteArray
  link : Bool
  deriving DecidableEq, Inhabited

/-- The invitation's bearer key pair, from the link's seed. -/
def Invite.bearer (i : Invite) : Device := Device.ofSeed i.secret
open Engine

/-- Byte order on ids. -/
def idLt (a b : Id) : Bool := decide (a.toList < b.toList)

/-- The better of two held acceptances: the admitted one, else the least
acceptance id. -/
def better (a b : Key × Id × Bool) : Key × Id × Bool :=
  if (a.2.2 && !b.2.2) || (a.2.2 == b.2.2 && idLt a.2.1 b.2.1) then a else b
open Engine Codec

/-- What a file's attachment says of it, sealed under the content key. -/
structure FileMeta where
  name : ByteArray
  kind : ByteArray
  w : Nat
  h : Nat
  preview : ByteArray
  deriving Inhabited, BEq

/-- A file to attach, with the fresh random bytes it needs: its own key
(32), the nonce it is sealed with (24), and the nonce its sealed info
is sealed with (24). -/
structure NewFile where
  info : FileMeta
  bytes : ByteArray
  key : Key32
  nonce : Nonce24
  metaNonce : Nonce24

/-- What the file's own seal is bound to. -/
def fileAd : ByteArray := "quiet/file/v1".toUTF8

/-- The file sealed under its own key: what the Merkle tree is over. -/
def fileCipher (f : NewFile) : ByteArray := cryptoSeal.enc f.key f.nonce fileAd f.bytes
open Engine

/-- The message a receipt's sort key names: its bytes past the two
counters (`recKey`). -/
def recMsg (sk : ByteArray) : ByteArray := ⟨(sk.data.toList.drop 16).toArray⟩

/-- A receipt list's bound for the rows past a, as `readable` names them
(by their messages, `asMsg`): a receipt row is past a when its sort key
is, or is a's and names a message past a's. The sort key decides, so
the bound is a key and the least id (`afterRec`, `beforeRec` and a
position's successor partition every list: `count_partition`). -/
def afterRec (a : Pos) : Pos :=
  (if bcmp (recMsg a.1) a.2 == .gt then a.1 else a.1.push 0, .empty)

/-- A receipt list's bound for the rows before b, as `readable` names
them: its sort key before b's, or b's and naming a message before b's
(so before a row's successor, the row itself is in: `anchor_read`). -/
def beforeRec (b : Pos) : Pos :=
  (if bcmp (recMsg b.1) b.2 == .lt then b.1.push 0 else b.1, ByteArray.empty.push 0)

theorem body_mkOp (reqs : List Id) (b : Body) : (Codec.decode (mkOp reqs b).body : Option Body) = some b :=
  Codec.decode_encode b

theorem shared_mkOp (C : Crypto) (reqs : List Id) (b : Body) :
    (family C).shared (mkOp reqs b) = !b.isLocal := by
  cases he : b.isEphemeral
  · cases hs : b.isLocal <;> simp [Family.shared, Family.room, family, scopeOf, body_mkOp, hs, he]
  · simp [Family.shared, Family.room, family, scopeOf, body_mkOp, he, Body.local_of_ephemeral he]
open Engine
section
variable {s : DB Fact} {C : Crypto}

theorem matching_also_nil (q : ListQ) (h : q.also = []) :
    matching s q = matching s { key := q.key, limit := q.limit } := by
  unfold matching; simp [h]

theorem mem_eval_matching {q : ListQ} {pf : Pos × Fact} (h : pf ∈ (Engine.eval s q).rows) :
    pf ∈ matching s q := by
  unfold Engine.eval at h
  simp only at h
  have h1 : pf ∈ (if q.desc then ((matching s q).filter fun p => q.inside p.1).reverse
      else (matching s q).filter fun p => q.inside p.1) := by
    unfold ListQ.cut at h; split at h
    · exact h
    · exact List.mem_of_mem_take h
  have h2 : pf ∈ (matching s q).filter fun p => q.inside p.1 := by
    split at h1
    · exact List.mem_reverse.1 h1
    · exact h1
  exact (List.mem_filter.1 h2).1

theorem mem_eval_all {q : ListQ} (ha : q.after = none) (hb : q.before = none) (hl : q.limit = none)
    {pf : Pos × Fact} : pf ∈ (Engine.eval s q).rows ↔ pf ∈ matching s q := by
  unfold Engine.eval ListQ.cut ListQ.inside
  simp only [ha, hb, hl, Bool.and_self]
  split <;> simp
end
open Engine

theorem rels_distinct : Rel.Distinct rels := by unfold Rel.Distinct; decide

theorem rels_short : ∀ r ∈ rels, r.kind.toUTF8.size < 128 := by decide
open Engine
variable {s : DB Fact} {C : Crypto}

/-- At rest, the Valid facts filed under a community relation. -/
theorem filed {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    (as : List ByteArray) (y : Id) (f : Fact) :
    (y ∈ s.idx (r.key as) ∧ s.status y = some (.valid f)) ↔ V C s.ops y f ∧ r.args f = some as := by
  exact filed_rel (fam := family C) rfl rels_distinct hr (rels_short r hr) h hq as y f
open Engine
section
variable {s : DB Fact} {C : Crypto}

/-- A row of a relation's list, read with any range, order and limit, is
a Valid fact filed in it, at its sort key and id. -/
theorem row_at {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    {as : List ByteArray} {lim : Option Nat} {desc : Bool} {after before : Option Pos} {pf : Pos × Fact}
    (hp : pf ∈ (Engine.eval s (r.query as lim desc after before)).rows) :
    pf = ((SortKey.sortOf pf.2, pf.1.2), pf.2) ∧ V C s.ops pf.1.2 pf.2 ∧ r.args pf.2 = some as := by
  have hm := mem_eval_matching hp
  rw [matching_also_nil (s := s) _ rfl] at hm
  obtain ⟨y, f, rfl, hy, hf⟩ := (mem_matching _ _).1 hm
  exact ⟨rfl, (filed (C := C) hr h hq as y f).1 ⟨hy, hf⟩⟩

/-- A Valid fact filed in a relation is a row of its whole list. -/
theorem at_row {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    {as : List ByteArray} {desc : Bool} {y : Id} {f : Fact} (hv : V C s.ops y f) (ha : r.args f = some as) :
    ((SortKey.sortOf f, y), f) ∈ (Engine.eval s (r.query as none desc)).rows := by
  have hf := (filed (C := C) hr h hq as y f).2 ⟨hv, ha⟩
  rw [mem_eval_all rfl rfl rfl, matching_also_nil _ rfl, mem_matching]
  exact ⟨y, _, rfl, hf.1, hf.2⟩

theorem admission_byUser_args {c u : Id} {f : Fact} :
    admission.byUser.args f = some [c, u] ↔ ∃ d e, f = .admission c u d e := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [admission.byUser, eq_comm]

/-- A row of a list read at rest is a Valid fact filed under it. -/
theorem row_filed {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    {as : List ByteArray} {lim : Option Nat} {p : Pos} {f : Fact}
    (hp : (p, f) ∈ (Engine.eval s (r.query as lim)).rows) : V C s.ops p.2 f ∧ r.args f = some as := by
  have hm := mem_eval_matching hp
  rw [matching_also_nil (s := s) (r.query as lim) rfl] at hm
  obtain ⟨y', f', he, hy, hf⟩ := (mem_matching _ _).1 hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact (filed (C := C) hr h hq as _ _).1 ⟨hy, hf⟩
end
open Engine
variable {s : DB Fact} {C : Crypto}

theorem byDevice_args {c d : Id} {f : Fact} :
    admission.byDevice.args f = some [c, d] ↔ ∃ u e, f = .admission c u d e := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [admission.byDevice, Root.byDevice, Rel.comap, Fact.admission?, eq_comm]
open Engine
section
variable {s : DB Fact} {C : Crypto}

/-- A list of distinct elements of M is no longer than M. -/
theorem nodup_sub_length_le : ∀ {l M : List Nat}, l.Nodup → (∀ y ∈ l, y ∈ M) → l.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, M, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ M := hs a (by simp)
    have ih := nodup_sub_length_le (M := M.erase a) hn.2 fun y hy => by
      have hne : y ≠ a := fun e => hn.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (hs y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem ha] at ih
    have : 0 < M.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- Distinct numbers below n: n of them exactly when all of them. -/
theorem nodup_full {l : List Nat} {n : Nat} (hn : l.Nodup) (hb : ∀ i ∈ l, i < n) :
    l.length = n ↔ ∀ i < n, i ∈ l := by
  constructor
  · intro hl i hi
    by_cases hni : i ∈ l
    · exact hni
    · have := nodup_sub_length_le (M := (List.range n).erase i) hn fun y hy => by
        have hne : y ≠ i := fun e => hni (e ▸ hy)
        exact (List.mem_erase_of_ne hne).2 (List.mem_range.2 (hb y hy))
      rw [List.length_erase_of_mem (List.mem_range.2 hi), List.length_range] at this
      omega
  · intro hall
    have h1 := nodup_sub_length_le hn fun y hy => List.mem_range.2 (hb y hy)
    have h2 := nodup_sub_length_le (l := List.range n) List.nodup_range
      fun y hy => hall y (List.mem_range.1 hy)
    rw [List.length_range] at h1 h2; omega
end
open Engine
variable {s : DB Fact} {C : Crypto}

theorem byKey_args {c e : Id} {f : Fact} :
    admission.byKey.args f = some [c, e] ↔ ∃ u d, f = .admission c u d e := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [admission.byKey, Root.byKey, Rel.comap, Fact.admission?, eq_comm]
open Engine
variable {C : Crypto}
section
variable {s : DB Fact}

/-- At rest, a row of a community relation's list, read whole, is
exactly a Valid fact filed in it, at its own id. -/
theorem mem_rows (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) {pf : Pos × Fact} :
    pf ∈ (Engine.eval s (r.query as)).rows ↔
      ∃ y f, pf = ((SortKey.sortOf f, y), f) ∧ V C s.ops y f ∧ r.args f = some as :=
  mem_rows_rel (fam := family C) rfl rels_distinct hr (rels_short r hr) h hq as

theorem eval_list {α : Type} (q : ListQ) (k : Answer Fact → View Fact α) :
    (View.list q k).eval s = (k (Engine.eval s q)).eval s := rfl

theorem better_cases (a b : Key × Id × Bool) : better a b = a ∨ better a b = b := by
  unfold better; split <;> simp
end
open Engine Codec

/-- The bytes `be64` lays out for n: digit i (base 256) for each i in is. -/
def digits (n : Nat) (is : List Nat) : List UInt8 := is.map fun i => (n >>> (8 * i)).toUInt8

theorem digit_toNat (n i : Nat) : ((n >>> (8 * i)).toUInt8).toNat = n / 256 ^ i % 256 := by
  simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- x + P·d against y + P·e, for x and y below P: by d and e, then x
and y. -/
theorem compare_place {x y d e P : Nat} (hx : x < P) (hy : y < P) :
    compare (x + P * d) (y + P * e) = (compare d e).then (compare x y) := by
  rcases Nat.lt_trichotomy d e with h | rfl | h
  · have : P * (d + 1) ≤ P * e := Nat.mul_le_mul_left P h
    rw [Nat.mul_succ] at this
    rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]; rfl
  · rw [Nat.compare_eq_eq.2 rfl]
    simp only [Ordering.then]
    rcases Nat.lt_trichotomy x y with h | rfl | h
    · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]
    · simp
    · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]
  · have : P * (e + 1) ≤ P * d := Nat.mul_le_mul_left P h
    rw [Nat.mul_succ] at this
    rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]; rfl

/-- k digits, most significant first, compare as the numbers mod 256^k. -/
theorem lexCmp_digits (a b : Nat) : ∀ k, lexCmp (digits a (List.range k).reverse) (digits b (List.range k).reverse) =
    compare (a % 256 ^ k) (b % 256 ^ k)
  | 0 => by simp [digits, lexCmp, Nat.mod_one]
  | k + 1 => by
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, digits, List.map_cons]
    have ih := lexCmp_digits a b k
    simp only [digits] at ih
    simp only [lexCmp]
    have hp : 0 < 256 ^ k := Nat.pow_pos_iff.2 (.inl (by decide))
    rw [Nat.pow_succ, Nat.mod_mul, Nat.mod_mul, compare_place (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)]
    have e1 : (a >>> (8 * k)).toUInt8 < (b >>> (8 * k)).toUInt8 ↔ a / 256 ^ k % 256 < b / 256 ^ k % 256 := by
      rw [UInt8.lt_iff_toNat_lt, digit_toNat, digit_toNat]
    have e2 : (b >>> (8 * k)).toUInt8 < (a >>> (8 * k)).toUInt8 ↔ b / 256 ^ k % 256 < a / 256 ^ k % 256 := by
      rw [UInt8.lt_iff_toNat_lt, digit_toNat, digit_toNat]
    rcases Nat.lt_trichotomy (a / 256 ^ k % 256) (b / 256 ^ k % 256) with h | h | h
    · simp only [e1.2 h, ite_true, Nat.compare_eq_lt.2 h]; rfl
    · have n1 : ¬ (a >>> (8 * k)).toUInt8 < (b >>> (8 * k)).toUInt8 := fun x => by have := e1.1 x; omega
      have n2 : ¬ (b >>> (8 * k)).toUInt8 < (a >>> (8 * k)).toUInt8 := fun x => by have := e2.1 x; omega
      simp only [n1, n2, ite_false, h, Nat.compare_eq_eq.2 rfl, ih]; rfl
    · have n1 : ¬ (a >>> (8 * k)).toUInt8 < (b >>> (8 * k)).toUInt8 := fun x => by have := e1.1 x; omega
      simp only [n1, e2.2 h, ite_false, ite_true, Nat.compare_eq_gt.2 h]; rfl

theorem be64_toList (n : Nat) : (be64 n).data.toList = digits n (List.range 8).reverse := rfl

theorem be64_length (n : Nat) : (be64 n).data.toList.length = 8 := by
  rw [be64_toList]; simp [digits]

theorem be64_len_eq (a b : Nat) : (be64 a).data.toList.length = (be64 b).data.toList.length := by
  rw [be64_length, be64_length]

/-- **Eight bytes, most significant first, order numbers below 2^64.** -/
theorem lexCmp_be64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    lexCmp (be64 a).data.toList (be64 b).data.toList = compare a b := by
  rw [be64_toList, be64_toList, lexCmp_digits, show (256 : Nat) ^ 8 = 2 ^ 64 by rfl,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem toList_append (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  rw [ByteArray.data_append, Array.toList_append]

theorem countCap_lt : countCap < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)

theorem min_lt {n cap : Nat} (h : cap < 2 ^ 64) : min n cap < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) h

theorem orient_map {α β} (f : α → β) (desc : Bool) (l : List α) :
    orient desc (l.map f) = (orient desc l).map f := by
  cases desc <;> simp [orient, List.map_reverse]
open Engine Codec
section
variable {s : DB Fact} {C : Crypto}

/-- The first row of a relation's list, read newest first with limit 1,
is at or after every fact filed in it. -/
theorem first_after {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    {as : List ByteArray} {y : Id} {f : Fact} (hv : V C s.ops y f) (ha : r.args f = some as) :
    ∃ y' f', (Engine.eval s (r.query as (some 1))).rows.head? = some ((sortOf f', y'), f') ∧
      V C s.ops y' f' ∧ r.args f' = some as ∧ Pos.cmp (sortOf f, y) (sortOf f', y') ≠ .gt := by
  have hm : ((sortOf f, y), f) ∈ matching s (r.query as (some 1)) := by
    rw [matching_also_nil _ rfl, mem_matching]
    have hf := (filed (C := C) hr h hq as y f).2 ⟨hv, ha⟩
    exact ⟨y, _, rfl, hf.1, hf.2⟩
  obtain ⟨t, ht, htm, hle⟩ := top_max rfl rfl rfl (by simp [Rel.query]) hm
  rw [matching_also_nil _ rfl, mem_matching] at htm
  obtain ⟨y', f', rfl, hy', hf'⟩ := htm
  obtain ⟨hv', ha'⟩ := (filed (C := C) hr h hq as y' f').1 ⟨hy', hf'⟩
  exact ⟨y', f', ht, hv', ha', hle⟩

end
end Community
