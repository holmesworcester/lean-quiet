# Quiet client 9.0.0 invariant-centric threat model

> **OWNER-APPROVED AUDIT MODEL — NOT A CONFORMANCE CLAIM.** This threat model
> was produced with AI assistance and approved by the engagement owner on
> 2026-08-31, with the private-channel, notification, and admission-acceptance
> formulations clarified on 2026-09-01,
> subject to the recorded review decisions. The completed audit found
> counterexamples to many of its intended guarantees. Treat each invariant as
> a falsifiable security requirement, not as evidence that Quiet satisfies it.

## Purpose, audience, and interpretation

This document defines what “secure” is intended to mean for the Quiet client
9.0.0 audit snapshot. It is written for Quiet developers and security reviewers,
using user-facing guarantees where possible and technical detail where it is
needed to make a guarantee testable.

This is an Invariant-Centric Threat Model (ICTM): each numbered security
invariant is a property users and developers should be able to rely on when its
preconditions hold. A reproducible violation is a security issue even if the
implementation behaves as designed. A widely expected property missing from
this document may also be a security or product-communication issue.

The invariants are **intended guarantees, not conformance claims**. Historical
formal-model counterexamples and brainstorm items remained hypotheses until
they were reproduced and independently validated against this exact target.
Final dispositions are recorded in `issues/confirmed/` and `issues/invalid/`;
the generated report is the finding index and narrative handoff.

## Version and scope

The model applies only to these immutable source revisions:

- Quiet superproject target: `7af0ad7989b6eff62944cfbe1453a62872c4c01f`
  (`audit-target-client-9.0.0` when the audit worktree was created);
- client local-first auth: `3rd-party/auth` at
  `32daff79ea4eb4265ae17183ed266aa2390c6a86`;
- Quiet Storage Service (QSS): `3rd-party/qss` at
  `db37831121ddb53200147c2ed5aabf237c74267f`;
- the auth copy built by QSS: `3rd-party/qss/3rd-party/auth` at
  `371e447f8dc892cb101eaffe1b8c7550c1556c8f`.

The security boundary includes the desktop and mobile clients, local backend,
local-first auth and CRDX graph, OrbitDB/IPFS replication and access control,
invitation and device-linking flows, QSS client integration and service,
notification paths, local persistence, and the client/server interfaces among
them. The exact file-by-file scope is recorded in `PROGRESS.md`.

The normative inputs are `QUINT-INVARIANTS.md`, `USER-INVARIANTS.md`,
`ICTM-REVIEW-DECISIONS.md`, and ordinary confidentiality, integrity, and
authenticity expectations. The public Quiet wiki threat model is older than the
formal/Quint work and is historical, non-normative context only.

Private PRs #80 and #93 are ancestors of the audited client-auth pin, and PR
#82 is an ancestor of the audited QSS pin. PR #81 is not an ancestor of the
audited superproject; the audit must establish behavioral integration rather
than assume it. These ancestry facts describe composition, not security.

## Vocabulary

- A **user** is the human/account-level principal.
- A **device** is a self-certifying device keypair belonging to exactly one
  user. A user's authority is exercised by an authorized, nonremoved device.
- A **member** is a user currently admitted to a particular Quiet community.
- `member` is also the conventional role that receives ordinary community
  content. It is not interchangeable with the member record above.
- An **admin** is a current member holding the protected `admin` role.
- A **server** is a self-certifying QSS server principal registered to a team.
  It is neither a user nor a device.
- A **sigchain** is Quiet's encrypted, signed, replicated authorization graph.
- A **lockbox** delivers a scoped key to a specific authorized recipient.
- **Causally before** means an operation is in another operation's signed graph
  ancestry, not merely concurrent with it or ordered before it by a local
  tie-breaker.
- **Surfaced content** is content the client accepts, indexes, displays, uses,
  or exports as valid—not merely opaque ciphertext it happens to relay.

## Assets and security outcomes

The model protects:

- users' and servers' private signing/encryption keys, device-link secrets,
  invitation seeds, community PSKs/salts, scoped content keys, and tokens;
- membership, role, device, server, invitation, lockbox, and key-rotation state;
- messages, attachments, profiles, notification credentials and previews,
  channel/community metadata, and their authorship and ordering;
- each replica's ability to converge on one authorized state and current
  members' ability to decrypt the content promised to them; and
- the separation between user, device, admin, private-channel, and server
  authority.

The intended outcomes are confidentiality (only the intended audience learns
content or secrets), integrity (unauthorized changes do not take effect),
authenticity (accepted data is bound to its real author and context), and
proportionate availability (malformed or cheap hostile input cannot cheaply
brick honest clients or QSS). Full availability against a party that can block
all communication is explicitly not promised.

## Usage scenarios and preconditions

The invariants below apply to these scenarios unless a narrower scenario is
named.

### S1 — Normal community use

An honest user creates or joins one community on an uncompromised supported
device, keeps private material secret, and runs the audited client. Current
members send and receive public-channel messages, attachments, profiles, and
metadata.

### S2 — Inviting and admitting a member

An authorized admin creates a member invitation and communicates the invite to
an intended invitee. The invitee creates and controls the private key for the
exact device it asks the community to admit. An authorized peer or registered
QSS assists the handshake. A registered QSS may complete admission from stored
graph/key material when no member is online, but cannot enlarge the roles or
keys preauthorized by the invitation.

### S3 — Linking another device

An existing member intentionally creates a device invitation for their own
user, and the new device proves possession of its newly claimed keypair. The
member understands that linked devices may receive that user's authorized
community keys and history.

### S4 — Public and private channels

Members use public channels; admins create and administer private-channel
membership. Private-channel participation uses a separate role and key scope,
but every current community admin is necessarily a member/participant of every
private channel and receives its complete history. Authenticated membership,
participant display, message and management authorization, and key delivery
must all reflect that same set, whether admin participation is materialized in
each channel role or derived canonically from the admin role. A non-admin
participant added by an admin receives all channel history; only an admin may
later remove a participant, and a current admin cannot be removed from only one
private channel. This admin-participation rule does not apply to DMs.

### S5 — Removal, revocation, and rotation

An authorized actor removes a member/device/server, revokes a role or
invitation, or changes/rotates keys. Honest clients may be offline during the
change and later merge concurrent or out-of-order graph and content data. The
required outcome is eventual loss of connectivity, new write authority, and
replacement keys once removal is universally reflected in valid group state;
the model does not require timestamp-based rejection of backdated or concurrent
content.

### S6 — QSS-assisted and notification use

Clients use a configured QSS for auth relay, offline encrypted-log retention,
fanout, and push notification support. QSS, its database, or a push provider may
be compromised. Clients still perform end-to-end cryptographic and application
validation. Push infrastructure receives a wake-up free of user-created content:
silent/data-only where supported, with a fixed generic iOS NSE envelope allowed
where needed. The trusted device performs a background history fetch and local
decryption. A successful local notification identifies the authenticated
message author and channel. The user's operating-system settings determine
lock-screen visibility.

### S7 — Restart and recovery

An honest client restarts with locally persisted sigchain, keyring, OrbitDB,
pending-entry, peer, QSS cursor, dead-letter, and native shared state. It may
then receive duplicates, missing parents, and older or newer data in arbitrary
network order.

### Preconditions common to intended guarantees

- The honest user's device and operating system are not already fully
  compromised, and the user has not intentionally disclosed the relevant
  private keys or invite secrets to the attacker.
- The audited cryptographic primitives, secure randomness, hash functions, and
  supported platform implementations behave according to their documented
  security assumptions.
- The attacker cannot break modern cryptography, guess high-entropy secrets, or
  find practical hash collisions.
- At least one honest path eventually supplies all required valid data for an
  eventual-convergence or recovery guarantee. Safety guarantees still apply
  when every transport withholds, duplicates, or reorders data.
- “Authorized” always means authorized by the valid causal sigchain state for
  that exact community and action, not merely recognized by UI state, QSS
  socket labels, unsigned metadata, or a different replica's later state.

## Adversaries

Adversaries may collude unless an invariant explicitly says otherwise.

- **NETWORK** controls network delivery. It can observe, intercept, replay,
  reorder, duplicate, delay, drop, and inject traffic; run arbitrary libp2p,
  Socket.IO, HTTP, IPFS, and OrbitDB peers; and present hostile invite links.
- **OUTSIDER** is not a member but may know public endpoints, team/community
  identifiers, captured ciphertext, and material intentionally exposed by a
  member. It may run many devices and connections.
- **INVITEE** possesses a valid or copied invitation link/seed but has not been
  admitted. It may race multiple admitting peers or reuse observed handshake
  material.
- **MEMBER** controls one or more authorized devices of an ordinary current
  member and all content/keys legitimately delivered to that member. It may be
  outside a target private channel.
- **REMOVED** previously was a member, device, role holder, channel participant,
  invitee, or server and retained everything legitimately learned before the
  effective removal.
- **ADMIN** is a malicious current admin. It can exercise genuine documented
  admin powers and is an intended participant in every private channel, but
  must not gain powers outside them, forge other authors, be omitted from the
  authenticated private-channel participant view, or obtain access to a DM
  solely through admin status.
- **QSS** fully controls a configured QSS instance, its persisted data, its
  server private keys, socket behavior, cursors, and responses. It may collude
  with NETWORK, OUTSIDER, INVITEE, MEMBER, or REMOVED.
- **LOCAL** can read or modify some local persisted files, logs, IPC/socket
  inputs, backups, or notification payloads, but does not begin with arbitrary
  code execution in the trusted client process or access to every OS-protected
  key.

For this model, the packaged backend, Electron main/preload/renderer code, and
native bridge code that legitimately receive live application secrets are part
of the trusted client process. An untrusted webpage or neighboring local
process that lacks the per-launch secret remains LOCAL. OS keychain and sandbox
access controls are assumed to enforce their documented boundaries; ordinary
application-data files and backups are not assumed to provide such a boundary
unless Quiet encrypts or explicitly excludes their sensitive contents.

Useful classes:

- **UNAUTHORIZED** = {NETWORK, OUTSIDER, INVITEE, REMOVED};
- **INSIDER** = {MEMBER, REMOVED, ADMIN};
- **INFRASTRUCTURE** = {NETWORK, QSS};
- **ACTIVE-INPUT** = every adversary above when it can supply serialized,
  persisted, protocol, database, file, or notification input.

An invariant written against a class applies to each named adversary in that
class and to their stated collusions.

## Security invariants

### A. Sigchain authenticity and identity binding

**A1 — The signed ciphertext is the entire authoritative link body.** Every
accepted sigchain link has a cryptographic signature over its ciphertext, and
every field that can affect its meaning—including action, signer, target,
identity, role, scope, key generation, lockbox plan, timestamp, team, and causal
parents—is recovered from or unambiguously bound to that signed ciphertext.
Unsigned outer fields may help route or decode a link but can never change its
reduction, authorization, attribution, decryption, or displayed meaning.

**A2 — Verification and authorization precede effect.** Before any link can
mutate state, release keys, authorize content, enter a cache, or be treated as a
valid parent, the client verifies the signature and proves that the signer is
the active device or server authorized for that exact action at the relevant
causal point. Rejected or unverifiable data has no security-relevant side
effect.

**A3 — All names identify the verified key.** Every redundant identity field is
bound to the same verified principal. In particular,
`payload.device.userId`, the device ID, claimed user/member, server ID, OrbitDB
writer, encrypted-signature author, team ID, and any outer object key must agree
with identities derived from or registered to the verified signing key. An
attacker cannot substitute a key while retaining a victim's identifier.

**A4 — Signatures and proofs cannot cross domains.** Identity challenges,
sigchain links, team messages, invitation proofs, device-possession proofs,
OrbitDB objects, NSE challenges, JWTs/UCANs, server actions, and legacy
certificates use unambiguous, distinct domains. Their signed transcript also
binds every context needed to prevent reuse—such as protocol version, team,
action/claim kind, signer kind, session nonces, and intended recipient—so a
signature obtained for one purpose cannot authorize another purpose, team,
session, principal type, or protocol version.

**A5 — Replay never grants fresh authority.** Replaying a valid signed link,
proof, acceptance, token, or application object cannot consume an invitation
again, add a second principal, restore revoked authority, advance a cursor over
unprocessed data, replace newer state, or cause the same logical operation to
take effect twice.

**A6 — User-visible authorship is cryptographic.** A message, attachment,
profile, channel object, community object, notification, or administrative
event is displayed or acted on as authored by user/device/server X only when
the accepted signed content and the verified writer identity both resolve to X
in that community. Display names, avatars, payload IDs, and service labels are
not proof of authorship.

### B. Complete mediation and authority separation

**B1 — Every sensitive state transition has one complete policy.** Every
emitter, validator, reducer, concurrency resolver, lockbox collector, restore
path, and Quiet/QSS wrapper enforces the same action-specific policy. There is
no generic, legacy, retry, server, or direct-graph path that bypasses it.

At minimum, complete mediation covers every running `TeamAction` separately:

| Action                          | Required intended author and authority                                                                                                                                                                                     |
| ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `ROOT`                          | The self-certifying founding device, exactly once, naming its derived founder and internally consistent generation-zero keys and roles                                                                                     |
| `ADD_MEMBER`                    | A current admin; this direct/test-helper path cannot bypass the invitation guarantees required of production admission                                                                                                     |
| `ADMIT_MEMBER`                  | A current member device acting as an admitting peer, or a registered server, but only as executor of an unexpired, unrevoked admin-issued member invitation plus the exact seed proof and device-possession proof in C1-C3 |
| `REMOVE_MEMBER`                 | A current admin, with the required scope rotations and removed-principal exclusion                                                                                                                                         |
| `ADD_ROLE`, `REMOVE_ROLE`       | A current admin; reserved roles, permissions, names, and affected keys remain protected                                                                                                                                    |
| `ADD_MEMBER_ROLE`               | A current admin; the sole self-grant exception is an invited member receiving exactly the roles preauthorized in the immutable admin-issued invitation during admission                                                    |
| `REMOVE_MEMBER_ROLE`            | A current admin; private-channel participant removal is admin-only and rotates the affected scope before subsequent content                                                                                                |
| `INVITE_MEMBER`                 | A current admin; its roles and policy are fixed in the exact immutable member invitation                                                                                                                                   |
| `REVOKE_INVITATION`             | A current admin, targeting the exact immutable invitation; any owner self-revocation rule for a device invitation must be documented explicitly                                                                            |
| `INVITE_DEVICE`                 | A current device of the owning user, creating an invitation bound to that same user                                                                                                                                        |
| `ADMIT_DEVICE`                  | A current member device acting as an admitting peer, or a registered server, but only as executor of the exact owner-bound device invitation and both proofs in C1-C3                                                      |
| `REMOVE_DEVICE`                 | The device's owning user; admin status does not permit another user's device recovery or manipulation                                                                                                                      |
| `CHANGE_MEMBER_KEYS`            | The owning user; admin status does not permit recovery or key changes for another user, and exact owner, generation, and replacement deliveries are bound                                                                  |
| `PUBLISH_USER_KEYS_TO_DEVICE`   | The newly registered receiving device, for its same owning user and only the USER-key deliveries authorized by that admission                                                                                              |
| `ROTATE_KEYS`                   | A current admin or other explicitly documented scope authority for the exact transition; no generic rotation conveys ambient authority                                                                                     |
| `ADD_SERVER`, `REMOVE_SERVER`   | A current admin, with the exact self-certifying server/team identity and required key rotation                                                                                                                             |
| `CHANGE_SERVER_KEYS`            | The authority explicitly approved for the registered server's rotatable keys; the initial review position is current-admin authorization unless B4 is deliberately expanded                                                |
| `SET_TEAM_NAME`, `SET_METADATA` | A current admin; metadata cannot redefine sigchain authority or protected role policy indirectly                                                                                                                           |
| `MESSAGE`                       | A current member device; the payload is never interpreted as an administrative command                                                                                                                                     |

The retired serialized `ADD_LOCKBOXES` action is never an authority-bearing
action: if recognized while replaying an otherwise accepted historical graph,
it is an inert no-op and cannot deliver ambient keys. This does not create a
peer/QSS protocol compatibility mode or weaken G7. Quiet-layer
channel creation/deletion and protected
channel metadata changes are current-admin actions. Adding or removing a
private-channel participant is current-admin-only; possession of the channel
role never conveys membership-administration authority.

**B2 — No role escalation or general self-grant.** Role grants are admin-only.
The sole self-grant exception lets a newly invited member acquire exactly the
roles and corresponding history keys that an admin cryptographically committed
to that member invitation; the invitee and QSS cannot choose or enlarge them.
`SET_METADATA`, `ADD_MEMBER_ROLE`, self-assignment settings, custom permission
maps, role-name collisions, copied lockboxes, and concurrent branches cannot
create an admin or admin-equivalent authority without an authorized admin
transition.

**B3 — Lockboxes are action-bound capabilities, not ambient authority.** A
lockbox is accepted only if its signed action authorizes that exact scope name
and type, generation, committed keyset, recipient type/identity/key, and old-to-
new state transition. A user cannot create, replace, pre-seed, copy, redirect,
or collect a lockbox for an ungranted scope or recipient relationship merely
because it decrypts or has the expected shape.

**B4 — Server and user authority are disjoint.** A server signature validates
only as the registered server for that team and only for the narrow server
actions the protocol assigns to it (currently admission assistance). A server
cannot act as a user, member, device, role holder, or admin; a user cannot act
as a server. Proof replay, harvested signatures, key substitution, signer-union
confusion, host labels, and socket-map labels cannot cross this boundary.

**B5 — Converged removal is enforced everywhere.** Once a valid
removal/revocation is universally reflected in the group state used by current
honest participants and QSS, the removed member/device/role holder/server loses
community connectivity, cannot author newly accepted actions or application
data, receives no replacement keys, and cannot use stale socket authorization.
Restart, replay, rollback, or a losing branch cannot restore that authority
without a fresh authorized re-admission or grant. This invariant does not
require detecting that a signed item was backdated or rejecting an item solely
because it was concurrent with removal.

### C. Invitation, admission, and device linking

**C1 — Seeing an invite is not device authority.** Admission validates two
distinct, jointly required proofs: a seed-derived invitation proof binds the
immutable invitation, exact team, member-versus-device claim, claimed user and
device, and protocol/session nonces; a separately domain-separated possession
proof is signed by the exact claimed device private key over that same claim
and session context. QSS, another member, an admitting peer, or anyone who only
saw the invite or either proof cannot substitute a device or gain admission.

**C2 — Invitations obey their policy exactly.** Invitation kind, author,
intended owner, role grants, expiry/revocation, and use count are immutable once
posted and checked atomically under concurrency. A member invite cannot be used
as a device invite or vice versa, and one permitted use cannot become multiple
admissions through racing, retrying, reconnecting, or alternative encodings.

**C3 — Admission has one recorded acceptance moment before secrets are
shared.** An existing member device or registered QSS accepts an admission by
validating and signing one `ADMIT_MEMBER` or `ADMIT_DEVICE` link containing the
admitted user/device information, atomically appending it to the accepted
sigchain, and durably persisting that state. This selected Option A transaction
completes before sending an accepted graph, keyring, starter/history keys,
joining an authenticated delivery room, or otherwise releasing member-only
material. No second online member is required, so a registered QSS may complete
this transaction alone. If it cannot complete, the invitee receives no
member-only material and cannot silently lurk.

**C4 — A valid admission cannot silently disappear.** Once an honest client has
accepted a valid admission and the same valid graph becomes available to honest
replicas, convergence retains that member/device unless an explicit authorized
removal wins under the documented convergent policy. A principal is never
simultaneously current and removed in converged state.

**C5 — Device links preserve one-user ownership.** A linked device is bound to
exactly the inviting user's record and its own proved keypair. It receives only
the user's currently authorized team/role/user keys and promised history. It
cannot be linked to another user, overwrite another device, or import more
authority than the user holds.

**C6 — Device removal cuts off future authority.** Removing a device prevents
that device from signing accepted new actions or receiving replacement keys.
Other current devices of the same user retain the user's intended access and
can recover after merge/restart without accepting state signed by the removed
device.

**C7 — Admins cannot recover another user's account or device.** Device
invitations, links, USER-key publication, and member-key changes remain bound
to the owning user and their proved devices. Admin authority over community
membership does not permit an admin to link a replacement device, publish USER
keys, rotate user credentials, or otherwise recover another user's account.

**C8 — A preauthorized invite works with QSS alone.** When no member device is
online, an invited member can complete the exact admin-preauthorized admission
through the registered QSS and receive all community and role history promised
by the invitation from stored encrypted graph/key material. QSS proves only
its narrow server role, records C3's admission, and cannot add roles, keys, or
history beyond the immutable invitation.

### D. Convergence, causal authorization, and recovery

**D1 — Equal valid input yields one state.** Honest replicas given the same set
of valid links derive the same membership, removed set, roles, devices,
servers, invitations, graph head, visible application authorization, and key
selection regardless of arrival order, restart, or which peer/QSS delivered
the links. No user is both current and removed.

**D2 — Honest and hostile histories cannot brick reduction.** A benign linear
history and every reachable accepted concurrent history reduce without
throwing, looping, or becoming permanently stuck. Missing, malformed, invalid,
or losing branches are rejected or quarantined without poisoning valid
descendants or preventing later honest progress.

**D3 — Grant/use ordering has one convergent authorization result.** A use of
membership, role, device, server, or invitation authority is accepted only if
the converged LFA history recognizes the required grant and every honest
replica reaches the same result. A losing, invalid, or absent grant cannot
authorize a use merely because of local arrival order. Whether every valid use
must causally descend from its grant, rather than follow a deterministic LFA
order, remains a lower-priority analysis question for this round.

**D4 — Removal converges to disconnection and loss of future authority.** Once
a valid removal is universally known in the converged state used by current
honest participants and QSS, the removed principal cannot remain connected,
write newly accepted application data or sigchain actions, or obtain replacement
keys. The model does not prioritize detecting backdated timestamps or rejecting
otherwise valid content solely because it was created or delivered concurrently
with removal. All replicas must nevertheless converge on one membership and
authorization result.

**D5 — Graph, authorization, and keyring state move atomically.** Merge,
admission, removal, rotation, persistence, and restore cannot leave the accepted
graph from one state paired with authorization or keys from another. A crash or
retry either preserves the last complete valid state or reaches the next
complete valid state; it does not resurrect stale access or lose an already
acknowledged security transition.

**D6 — Out-of-order application data waits for proof.** This is a firm
requirement: OrbitDB or other application content that arrives before the LFA
state needed to authenticate and authorize it is not surfaced or used. It may
be boundedly quarantined and retried once the required graph state arrives, but
it cannot become valid because of an unrelated future grant, reused identifier,
later team, or rollback.

**D7 — Eventual recovery does not weaken safety.** After duplicates, missing
parents, disconnection, QSS failover, restart, or offline operation, providing
the same complete valid inputs makes honest replicas converge and current
recipients recover the content promised to them. Recovery never skips signature
or authorization checks.

### E. Key confidentiality, availability, and removal

**E1 — Current recipients get the keys and history promised to them.** Every
current member can decrypt all community history promised by admission, and
every current admin and every newly added non-admin private-channel participant
receives all history for that channel. Admin promotion provides the existing
private-channel history implied by the new role. Concurrent changes, QSS-only
admission, rotation, a losing branch, multi-device use, or restart do not
strand intended content or make valid graph reduction fail.

**E2 — Nonrecipients do not get scoped keys or plaintext.** OUTSIDER, INVITEE,
QSS, and an ordinary MEMBER outside a private scope cannot decrypt that scope's
content or obtain its signing/encryption keys. Every current admin is an
intended private-channel recipient by definition; admin key delivery is
therefore permitted only when the authenticated participant state and all
application authorization surfaces consistently represent that membership.
Admin status alone confers no DM access.

**E3 — Converged removal provides future exclusion, not retroactive erasure.**
After removal is universally known in valid group state, replacement keys
exclude the removed principal and newly accepted content does not fall back to
an old generation. The model does not require classification or rejection of
content merely because it is backdated or concurrent with removal. Content and
keys already delivered to the removed principal may remain readable;
retroactive erasure is not promised.

**E4 — No silently dropped invitee receives member keys.** A nonmember,
including an invitee whose admission was not validly committed, receives no
team, role, channel, user, or history key intended only for current members.

**E5 — Key generations and manifests are unambiguous.** A scope cannot roll
back, reuse, replace, or confuse a generation or keyset commitment. Concurrent
rotations resolve consistently; losing key material cannot authorize or render
undecryptable a descendant that the converged graph accepts.

**E6 — Secret handling is least-privilege.** Private keys, invite seeds,
community PSKs/salts, scoped keys, notification credentials, and bearer secrets
do not appear in logs, errors, analytics, URLs beyond the intended invite,
world-readable storage, unrelated IPC, or unprotected backups. When a native
shared container or OS-protected backup must hold a secret for an implemented
feature, the data is minimized, encrypted or protected by the documented OS
boundary, and excluded when that boundary is unavailable. When authorization
ends, honest clients remove revocable credentials and local copies under their
control. This cleanup does not promise deletion from an adversary-controlled
device or backup, or erase keys legitimately delivered before removal under
E3. Exports and linked-device transfers contain only the minimum authorized
scopes and are validated on import.

### F. Application-data confidentiality, integrity, and authenticity

**F1 — Public-community content is member-confidential.** Public-channel
messages, attachments, member profiles, and member-only community/channel
metadata are plaintext only to current authorized community recipients under
the documented history/removal rules. NETWORK, OUTSIDER, INVITEE, and QSS may
relay ciphertext but cannot learn plaintext or keys.

**F2 — Private-channel content is participant-confidential.** Private messages,
attachments, user-created metadata, previews, channel keys, and the complete
channel history are plaintext only to the authenticated channel participants
and trusted local components needed to present them. That participant set must
include every current community admin. Other ordinary members, QSS, and push
providers cannot decrypt the channel. A newly added non-admin participant and
a newly promoted admin receive all prior channel history through the same
canonical participant scope. No valid state contains a nonparticipating current
admin; DMs retain their separate explicit participant set.

**F3 — Every accepted application object is fully bound.** The signed/encrypted
content binds its team, store, operation, object key/ID, author, channel or user,
scope and generation, timestamp/order fields, and security-relevant references
to the verified OrbitDB writer and decrypted payload. Changing an unsigned
envelope cannot cross-post, relabel, reorder, delete, or reattribute the object.

**F4 — Messages and attachments cannot be forged or silently altered.** An
attacker cannot insert, modify, replay as a new message, duplicate in the UI,
cross-channel, or delete another user's message without the exact documented
authority. Attachment bytes are bound to their authenticated metadata and
content identifier before opening, saving, or displaying. Transport
suppression remains subject to G5's availability limit.

**F5 — Channel state is consistent with its authorization scope.** A channel's
ID, team, owner, privacy class, role/scope, and immutable metadata cannot be
overwritten or recreated under an alias. Private-channel creation uses a fresh,
unambiguous scope. The authenticated participant predicate includes every
current admin and is identical for participant display, history/subscription,
message authorization, channel management, and key distribution. Adding or
removing another participant changes that same authorization and key scope.

**F6 — Only admins change private-channel membership.** Merely holding the
channel role or knowing its key does not authorize adding or removing a user.
Admin role state itself canonically entails membership in every private
channel. An admin's addition/removal of any other participant is a signed,
visible sigchain transition. Addition delivers every historical channel-key
generation; removal rotates the current channel key so the removed participant
receives no replacement key or newly accepted content once removal is
universally known. A current admin cannot be removed from one private channel
while retaining the admin role.

**F7 — Profiles are self-owned and authentic.** An ordinary member can change
only their own profile. Store key, payload user ID, decrypted user ID, signature
author, OrbitDB writer, team, and current membership identify the same user.
Any admin deletion power is explicit and cannot be used to forge a replacement
profile as the deleted user.

**F8 — Notification credentials remain device/user-bound.** Push tokens,
QPS/UCAN credentials, NSE challenges/JWTs, sequence state, and notification
keys bind the exact user, device, team, QSS, capability, endpoint, and validity
period. Other members cannot register, use, tombstone, or retain another
device's token. QSS and push providers receive no plaintext user-created field
or preview: the provider leg is free of user-created content, using a
silent/data-only wake-up where supported and only a fixed generic iOS NSE
envelope where needed. A trusted local device component fetches, authenticates,
and decrypts history, then renders at least the authenticated message author and
channel.
This decision does not prohibit additional locally decrypted message text, and
lock-screen visibility follows the user's operating-system settings. QSS and
push providers cannot forge authenticated notification content.

**F9 — Community metadata is admin-authentic.** Protected community metadata
and team name changes require the current admin authority. Legacy root/owner
certificate compatibility cannot override current sigchain authority, forge a
current admin, or let unsigned data control security policy.

**F10 — File handling preserves host integrity.** Authenticated attachment
metadata and remote blocks cannot escape the intended storage directory,
overwrite/delete unrelated files, trigger unsafe decoding or automatic opening,
or consume disproportionate resources. Filename, path, type, size, dimensions,
CID/hash, team, channel, and author are validated before security-relevant use.

**F11 — User-created metadata is content-confidential.** QSS, push providers,
and other third parties receive no plaintext user-created field, including user
or profile names, community/team names, channel names or descriptions,
filenames and file metadata, messages, captions, or previews. Those fields are
encrypted and authenticated as content. Protocol and traffic metadata—such as
timestamps, hashes/CIDs, opaque principal/team/store identifiers, cursors,
ciphertext sizes, endpoints, online state, and routing/relationship information
inferable from traffic—is outside the QSS-metadata confidentiality guarantee.
Errors, logs, retries, and push payloads do not turn a user-created field,
plaintext, key, or invite seed into allowed operational metadata.

### G. Malicious QSS, network, and external-service safety

**G1 — QSS is an untrusted relay for end-to-end content.** A malicious QSS can
store, replay, reorder, omit, or fabricate opaque entries, but clients accept
and surface only entries independently passing OrbitDB identity, end-to-end
signature, scope, team/channel, causal, and application authorization checks.
QSS sequence numbers, acknowledgements, database IDs, room membership, and
outer labels are never proof of content validity.

**G2 — QSS compromise does not confer community authority.** QSS cannot become
a user/admin, grant roles, change metadata, forge application authorship, or
admit a principal without the exact valid invitation/device proof and recorded
server authority. Compromise of one server identity does not authorize another
team, QSS instance, user, device, or action domain.

**G3 — Socket identity and team context cannot diverge.** Every QSS graph, log,
push, token, or community action binds the live authenticated LFA principal,
socket, connection-map entry, room, sigchain team, request team, configured
server, and persisted community. Attacker-chosen `userId`, team ID, host label,
or reconnect state cannot substitute for that binding or evict/reuse another
principal's authenticated session.

**G4 — QSS cannot read unauthorized content.** QSS may receive ciphertext and
the operational metadata permitted by F11, but it receives no end-to-end team,
role, private-channel, attachment, or user private key that its narrow server
role does not require. It cannot decrypt messages, attachments, user-created
names or file metadata, profiles, or private previews merely by storing them or
assisting admission.

**G7 — Breaking protocol versions fail closed.** The client, peers, and QSS
bind and compare the main/major protocol version before exchanging authoritative
graph, keys, or application data. A mismatch for a breaking change aborts the
session without legacy parsing, downgrade, partial registration, or a backwards-
compatibility mode.

**G5 — Withholding harms availability, not safety.** NETWORK or QSS may prevent
progress by indefinitely blocking all honest communication; continuous service
is not promised in that case. Omission, equivocation, rollback, duplication, or
reordering cannot make invalid state appear authorized, resurrect removed
authority, or permanently prevent convergence once complete valid input becomes
available from an honest path.

**G6 — Native notification paths enforce equivalent context.** iOS/Android
notification code uses compatible cryptographic formats and distinct domains,
checks current device/team/QSS identity and removal, and authenticates/decrypts
before displaying the required message author and channel, any locally selected
message text, or advancing durable cursors. A malicious QSS, Firebase/APNS
payload, or stale JWT cannot make the extension show forged attribution/content
or leak another scope. Platform/user notification settings, rather than a
provider-supplied field, govern locked-screen presentation.

### H. Persistence and proportionate availability

**H1 — Restore never turns stale or corrupt data into authority.** Persisted
sigchains, keyrings, OrbitDB state, pending entries, tokens, cursors, dead-letter
queues, keychain data, and native shared defaults are validated for format,
version, team, identity, signature, generation, and causal consistency before
use. Rollback or partial state cannot restore removed authority or pair current
content with stale keys.

**H2 — Untrusted input fails closed and locally.** Malformed, oversized, deeply
nested, cyclic, missing-parent, duplicate, or unsafe-key input is rejected or
boundedly quarantined without uncaught exceptions, stack exhaustion, prototype
pollution, persistent corruption, or process-wide failure. One bad peer, entry,
invite, message, file, or notification does not block unrelated valid work.

**H3 — Cheap hostile work is bounded.** Before authentication and cheap
shape/size checks, an attacker cannot cause disproportionate decoding, hashing,
signature verification, resend timers, retries, graph traversal, pending/DLQ
growth, database/storage use, socket/listener growth, bandwidth, or external-
service cost. Limits and cleanup apply per peer/session/team as appropriate.

**H4 — Positive-control operation remains usable.** Ordinary all-honest
community creation, invitation, admission, messaging, private-channel use,
device linking, removal, offline merge, and restart complete successfully.
Security checks cannot satisfy the model vacuously by rejecting all input,
never admitting anyone, or never surfacing content.

**H5 — Local command channels authenticate their caller.** An untrusted webpage
or neighboring local process without the per-launch credential cannot invoke
backend Socket.IO, IPC, deep-link, or native-bridge actions or read their
responses. Credentials are origin/channel-bound where applicable, are not
exposed to unrelated content, and expire with the application session. Full
compromise of a trusted renderer/main/backend/native process remains outside
the model; hostile payloads received through an authenticated channel remain
untrusted and still require action-level validation.

### I. Libp2p, Tor, IPFS, and OrbitDB

**I1 — The community PSK is not membership or application authority.** Knowing
the libp2p PSK or an invite/bootstrap address may permit an attempted transport
connection, but it never proves LFA membership, user/device identity, channel
membership, write authority, or entitlement to keys/content. Invitees and
removed members that retain the PSK remain subject to the same LFA and
application authorization checks.

**I2 — Every P2P transport path enforces the intended network boundary.** Tor,
onion addresses, libp2p connection protection, Noise/transport authentication,
WebSocket listeners, relays, bootstrap, reconnect, migration, and platform-
specific paths do not silently downgrade to a clearnet or unprotected swarm.
PSKs, onion-service secrets, and invite/bootstrap secrets are handled under E6.

**I3 — Transport identity never substitutes for LFA identity.** A libp2p
PeerId, Noise/TLS key, onion address, multiaddr, pubsub author, QSS socket label,
or connection-map key is routing/transport data. Any application or sigchain
authority is independently bound to the exact authenticated LFA
user/device/server and team under A3, B4, and G3.

**I4 — IPFS provides bytes, not application authorization.** A CID/hash must
match the retrieved bytes, but CID validity alone does not prove team, channel,
file, author, scope, or message authorization. Attachment bytes and every
user-created filename or file-metadata field remain end-to-end encrypted and
bound to the authenticated application object before use.

**I5 — Every OrbitDB ingestion path applies the same gates.** Direct peer sync,
pubsub fanout, IPFS block retrieval, QSS replay, pending-entry retry, and
database reopen bind the OrbitDB identity, database address/manifest, access
controller, operation, entry signature, LFA principal/team state, encrypted
application author, and object/store scope consistently. D6 applies on every
path: missing authorization state delays use rather than weakening validation.

**I6 — P2P partition and Sybil behavior cannot violate safety.** A malicious
bootstrap, DHT, pubsub, relay, IPFS, OrbitDB, or PSK-holding peer may eclipse,
delay, replay, or suppress data and thereby deny progress. It cannot make
unauthorized state valid, create divergent accepted authority from equal valid
input, restore a removed principal after convergence, or prevent recovery once
a complete honest path returns.

**I7 — P2P work and storage are proportionately bounded.** Connection attempts,
Tor circuits, Noise/LFA handshakes, peer discovery, identify/DHT/pubsub traffic,
graph/head exchange, Bitswap/IPFS requests, OrbitDB entries, pending blocks,
pinning, retries, and per-peer queues have early validation, resource limits,
cleanup, and isolation sufficient for H2/H3.

## Explicit design non-goals and limitations

These are limits on what users should rely on, not confirmed implementation
vulnerabilities.

- **No retroactive erasure or backdating guarantee.** Removing a
  member/device/role does not erase plaintext, ciphertext, keys, screenshots,
  exports, or backups already delivered before removal. The model does not
  promise to identify backdated content or reject content solely because it is
  concurrent with removal. It promises converged disconnection, loss of new
  write authority, and exclusion from replacement keys under B5/D4/E3.
- **No availability against total suppression.** NETWORK, QSS, an ISP, Tor
  failure, or a malicious admin exercising genuine removal/channel-deletion
  authority can deny service. The model protects safety and recovery once an
  honest communication path and complete valid data are available.
- **No protection after full endpoint compromise.** Malware or physical/OS
  compromise that can read the live trusted process, unlocked keychain, screen,
  or keyboard can steal plaintext and keys or act as the user. LOCAL covers
  partial persisted/input access, not arbitrary trusted-process execution.
- **Admins have disruptive documented power.** A malicious admin may perform
  actions the policy genuinely grants, such as admitting/removing members and
  administering channels, and is entitled to read every private channel. The
  audit checks that these powers are signed, visible, correctly scoped,
  reflected consistently in private-channel membership, and cannot forge
  another principal or confer implicit DM access.
- **Possession of a live invite link is intentional invite capability.** Invite
  secrecy helps restrict who can attempt admission, but invite possession alone
  must still not substitute for proof of the admitted device key (C1).
- **QSS/traffic metadata privacy is out of scope.** Tor and encrypted payloads
  do not promise that timing, hashes, CIDs, volume, online status, endpoints,
  opaque identifiers, team association, or routing relationships are hidden
  from a global observer, QSS, or push infrastructure. This does not permit
  plaintext disclosure of any user-created field protected by F11.
- **Third-party platform compromise is only partially contained.** QSS,
  Firebase/APNS, PostgreSQL, Redis, cloud secret storage, and OS backup systems
  may retain the provisional operational metadata intentionally given to them
  and encrypted records they carry. This does not relax E6 for plaintext keys
  or secrets. The model requires least privilege and end-to-end content safety
  but does not claim those services are always available or erase permitted
  operational records instantly.
- **Direct messages are not implemented in this snapshot.** UI/parser
  placeholders are not a DM security design. No current DM confidentiality,
  integrity, authenticity, membership, history, or rotation guarantee is
  claimed.

## Implementation status and audit evidence

These composition facts guided the review and remain relevant to interpreting
the final findings:

- the target is a separately assembled audit branch rather than the current
  `private/develop` tip;
- private PR #81 is not an ancestor of the target, so equivalent Quiet-facing
  integration must be checked path by path;
- QSS builds an auth revision three commits behind the client auth revision,
  making mixed-version protocol behavior a required integration check;
- the formal/Quint source documents counterexamples in an earlier design for
  authorship, membership convergence, admin promotion, graph progress, and key
  confinement; those are regression targets only;
- existing `securityCandidates` and related PoC tests were treated as
  hypotheses and positive/negative controls; a passing PoC alone was never
  considered a confirmed production vulnerability without realistic
  reachability and impact validation.

The completed file-by-file, global, proof, and independent-validation records
are under this audit state directory. Confirmed weaknesses are in
`issues/confirmed/`, rejected hypotheses and their reasoning are in
`issues/invalid/`, and phase completion is recorded in `PROGRESS.md`. The final
generated report incorporates those canonical dispositions.

## Approved review decisions

The engagement owner approved this model on 2026-08-31 and clarified its
private-channel, notification, and admission formulations on 2026-09-01 with
these decisions:

- removal is convergence-based under B5/D4/E3; backdating and strict rejection
  of concurrent content are not priority guarantees;
- D6 must hold, while stricter cross-system causal grant/use rules are a lower
  priority for this round;
- every current admin is a participant in every private channel,
  private-channel additions and removals are admin-only, and every new
  participant receives all channel history; this admin implication does not
  apply to DMs;
- admins cannot recover, link, publish keys for, or change keys for another
  user's account/devices;
- invitation-bound admission is the only self-grant and conveys only the exact
  admin-preauthorized roles and history, including when QSS is the only online
  admitting party;
- QSS/third-party confidentiality covers every user-created field, but not
  times, hashes, opaque identifiers, sizes, or traffic/routing relationships;
- push infrastructure receives a wake-up free of user-created content, using a
  silent/data-only form where supported and only a fixed generic iOS NSE
  envelope where needed; a trusted device performs the background fetch and
  local decryption, then displays at least the authenticated author and channel,
  with lock-screen visibility governed by the user's operating-system settings;
- admission uses Option A: the admitting member/QSS validates, signs, atomically
  appends, and durably persists `ADMIT_*` before releasing graph or keys; no
  second online member is required. A witnessed/admin-approval gate is only a
  possible future optional community setting;
- breaking main/major protocol-version mismatches fail closed with no backwards
  compatibility mode; and
- `user`, community membership/member record, device, and the conventional
  `member` role are distinct terms. Audit findings should use them consistently
  and flag ambiguous target code/documentation for later remediation without
  rewriting the immutable audit target.

## Remaining non-blocking design questions

1. **Silent omission detection:** Define what a client can claim about being
   fully synchronized when a malicious QSS is its only reachable source. Total
   suppression remains an availability non-goal.
2. **DM design:** Before implementing direct messages, define participant and
   device sets, multi-device linking, membership change/removal, history
   sharing, metadata privacy, attribution, replay, and key-rotation invariants,
   then repeat security review.
3. **Local boundary and backups:** Confirm which renderer, preload, native
   extension, local process, keychain/shared-container, and backup components
   are trusted and which at-rest confidentiality and rollback guarantees LOCAL
   receives. H5 is the current approved audit position.

## Future maintenance

This model must be revised whenever remediation, protocol behavior, intended
policy, a new QSS capability, private-channel change, device-linking change, or
DM implementation changes the guarantees.
Removing or weakening an invariant is a security-relevant compatibility change
that must be explicit in release notes and user/developer documentation.
A future optional “joiners require admin approval” community setting must define
its witnessed acceptance transaction separately; it does not weaken the current
Option A default or permit pre-persistence graph/key release.
