# lean-engine

A persisted op engine in Lean 4, with libquiet's validity model, a
community family on top, and proofs that reach from SQLite rows to
high-level guarantees about membership, removal, impersonation,
connection and sealing. A first pass: deletion, channels,
key rotation and a transport are not here yet.

## The engine (`Engine/`)

An op names the ops it requires. Its verdict is inductive and local,
as in libquiet's DESIGN.md: an Invalid requirement makes it Invalid;
once all are Valid, its validator reads the facts they produced and
accepts (producing the op's fact) or refuses. Anything else waits.

`Core.lean` is the code that runs: `ingest` stores and queues an op,
`step` judges one queued op, waking what waited on it. Every table goes
through `Store`, which has two instances: SQLite (`Sqlite.lean`, the
real one) and a pure model (`Model.lean`, for proofs). Nothing lives in
memory between steps; one write turn is one `BEGIN IMMEDIATE`
transaction.

Proven (`Proofs.lean`), about that code run on the model:

- `inv_ingest`, `inv_step`: the tables keep `Inv` through any
  interleaving of arrivals and steps (so through any crash, which
  leaves a committed state).
- `status_iff_spec`: at rest (queue empty), the persisted verdicts are
  exactly the declarative spec's (`Spec.lean`: the least fixpoint of
  `judge`), and the index holds exactly the Valid facts' keys.
- `same_ops_same_verdicts`: two nodes that received the same ops, in any
  order and batching, both finish processing and then hold the same
  verdict (fact included) for every op. (`order_free` is the at-rest
  half.)
- `drain_bounded`, `step_budget`: draining with the budget the writer
  reads off its tables (queue length + undecided ops × stored ops)
  empties the queue; the write path has no `partial` loop.
- `drain_terminates`, `drain_settles`: op processing terminates — from
  any reachable state, finitely many steps empty the queue, and then
  every verdict is the spec's.
- `spec_extends`: a verdict, once reached, never changes.
- `Codec.decode_encode`: what SQLite stores decodes to what was written.
- `Codec.encode_decode`: decoding is strict; bytes decode only if they
  are exactly their value's encoding, so a value has one byte string
  wherever it is read (SQLite, the wire, an op's body, a link).
- `Op.id_decode`: an op read from bytes has the SHA-256 of those bytes
  as its id. An op's bytes are the same on the wire and in its SQLite
  row, and nothing can build an op under another id (`Op.id_eq`).
- `distinct_of_collisionFree`: ops share an id only through a SHA-256
  collision on their bytes, so `Distinct` asks nothing of peers.

### Declarations: relations by name (`Decl.lean`)

A fact kind declares the lists its facts are filed in, as relations
named `<kind>.<name>` (`admission.byDevice`, `removal.byUser`, ...), each
with the key arguments of a fact in it. A relation's key is its names
and those arguments, so keys are named, never numbered; a family's keys
are its relations' (`keysOf`). Laws, proven once for every relation:

- `mem_keysOf`: with distinct names (checked by `decide` for the
  community's list, `rels_distinct`), a fact is filed under r's key at
  `as` exactly when it is in r at `as`.
- `Rel.key_ne_opKey`: a relation key is never an op's own key.
- `filed_rel`, `mem_rows_rel`, `total_rel`: at rest, a list of r reads
  exactly the Valid facts in it.

### A device's own state, and intents (`Facts.lean`, `Intents.lean`)

Everything about joining and bootstrapping is op state. A device's own
state is local ops: its secret seed (`secret.byKey`, refused unless the
seed derives to the key: `secret_derives`), the communities it is in
(`accepted.all`) and its pending joins (`joining.all`); a community's
name is a shared admin register (`named.current`, newest counter first:
`named_by_admin`). An intent is a user action as the ops of one writer
job, after reading lists: `found`, `inviteTo`, `join` (with the name to introduce itself by), `approveReq`
(the approval, and the admission when it completes the tally),
`introduce` (the first profile, once admitted), `stopWaiting` (a local
`abandon` of a pending join; an approval still admits), `rename`, `send`
(blobs and the post), `reactTo`. Laws: `join_travels`
and `found_travels` (of those ops, only the request, or the root, the
name and the founder's profile, may travel), `local_fact_mine` (every Valid secret, acceptance
or pending join a node holds is its own write, whatever peers send).
`Tests/Lifecycle.lean` runs it on two SQLite nodes.

### The invite link (`Link.lean`)

`quiet://join/` and the fields in base62: community, invitation, the
inviter's device key, dial hints, the bearer seed. `parse_text`, and
`parse_valid` (whatever parses is valid).

### Sync scope (`Sync.lean`)

Each op is shared or local (`Family.scope`, read from its body, never
from the header's kind). Local ops are a node's own bookkeeping: judged
and stored like any op, never sent or taken.

- `offer_shared`, `offer_stored`: sync offers only stored ops of shared
  kinds, so never a local op and never a write still in the outbox.
- `intake_local`, `stored_local`: a peer's job passes `intake`, which
  drops local ops; so every local op a node stores is one of its own
  writes, whatever its peers send.

### Reading: lists and views (`Query.lean`, `View.lean`)

There is one read, a list: the Valid facts filed under a key (and
optionally under other keys too), in sort order, within a range, at most
`limit` of them (`none`: all), each row with its fact, plus counts.
Every Valid fact is also filed under its op's own key (`opKey`), so
reading one fact is a list of one. `Lists` has two instances: `listSql`
on SQLite and `eval` on the model; `querydiff` checks them equal.

A view is a value composed of lists, where later lists may depend on
earlier answers (`View`). It runs on either instance, and the keys it
watches are the keys of the lists it read: nothing is recorded.

- `eval_stable`: a list's answer changes only if a row is filed under
  its key (its other conjuncts need no watching: a fact's keys are filed
  together when it is decided).
- `view_stable`: so a view's answer changes only if a row is filed
  under a key it read. Notices for exactly those keys are complete;
  `querydiff` checks it on SQLite after every commit.

## The community (`Community/`)

Root (founder, admin), invite (with an approval threshold), request,
approve, admit (member or linked device), admin grant, removal, post,
wrap — after libquiet's DESIGN.md and its removal stack (#778, #98,
#1088). A request is libquiet's Join before its vouches: it carries the
bearer key's and the device's signatures and admits nobody. Approvals
are signed ops that cite it (so the engine needs no forward needs), and
an unsigned admit op tallies exactly the invitation's threshold of them,
by distinct users, into the admission. A link invitation needs one
approval, by the issuer's user; nobody approves their own request. Validity reads only cited facts, so every
admin-issued removal stands: of other admins, mutually, and by an admin
who has since been removed, and an approval by a user removed since
still counts. In practice that last kind may not spread,
since peers who know of the remover's removal refuse its devices; but
wherever it arrives, it is Valid. Removal never invalidates an op; it
changes who counts.

Laws (`Laws.lean`, `Connect.lean`):

| question | law |
|---|---|
| Are all messages by admitted users? | `message_authorized` |
| Is impersonation impossible? | `no_impersonation` (given unforgeable signatures), `admission_consented` |
| Can outsiders join? | `admission_needs_approval` (every admission but the founder's cites a member's approval), `admission_approved`, `request_invited`, `approval_signed`, `invitation_issued` |
| Are requests with their approvals admitted? | `request_valid`, `approve_valid`, `admit_admits`; `removed_approver_admits` (a removed member's approval still counts) |
| Who may remove whom? | `removal_authorized`, `admin_removal_stands`, `mutual_removal`, `admin_granted` |
| Can a removal be undone, or rewrite history? | `removed_stays`, `valid_stays` |
| Do we connect to non-members or removed members? | `connect_iff`, `refuse_nonmember` |
| Whom do we dial? | `members_iff` |
| Do we connect to approved devices, and only those? | `connect_admitted`, `connect_approved` (a pending request never connects) |
| Who is a new content key sealed to? | `recipients_iff` |
| What does a removal cut off? | `removal_cuts_off`, `connect_agree`: the removed user's devices plus any nodes that have not yet received the removal |

The connection, dialing and sealing laws are about the views
themselves (`allowPeer`, `members`, `recipients`, in `Query.lean`), lists
read over the persisted tables: `admission.byDevice`, `admission.all`,
and each named user's `removal.byUser`.

## What is assumed, not proven

- SQLite behaves like the model (untampered, atomic). Tested:
  `differential` compares every table row for row under random
  workloads and schedules; `crash` kills the writer with SIGKILL and
  checks the disk holds whole batches.
- Signatures are unforgeable (`Unforgeable`, a hypothesis where used).
  Ed25519 is libsodium's at runtime.
- SHA-256 has no collision on the ops a node holds (`CollisionFree`,
  which gives `Distinct`). `wire` tests a lying peer against it: forged
  names, padded op bytes, and a signed post re-padded into a new id.
- `Crypto.pub` gives a seed's public key (libsodium's Ed25519 at
  runtime); a secret op is Valid only if its seed derives to its key.
- The SQLite writer drains with the proven `drain` and a budget it
  counts in SQL (`budgetSql`); that the count equals `Engine.budget` is
  tested (`differential`), and `drain_bounded` proves that budget
  empties the queue.
- Confidentiality is proven as "who keys are sealed to", not as a
  cryptographic property, and removed users keep keys they already
  hold: no rotation yet, as in libquiet's current increment.

## Running

    mise run check   # build proofs, audit axioms (standard only)
    mise run test    # scenario, differential, querydiff, linkcheck, lifecycle, wire, crash

Needs `ELAN_HOME` with Lean 4.34.0, and SQLite and libsodium (headers
for SQLite). The CI workflow runs both tasks; this repo has no remote
yet.

## Sync

Two nodes reconcile with Merkle RBSR over claimed-time windows, stream
new ops between rounds, and send requirement closures: design, laws and
follow-ups in [docs/SYNC.md](docs/SYNC.md).

## The connection family

Connecting is ops the engine judges, as in poc-17 and tiny (poc-13).
The daemon only moves bytes. Everything else is engine code
(Engine/Sync/Node.lean, Engine/Purge.lean, Engine/Families.lean) or op
code (Connection/, one file per op type).

- **Handshake.** Noise_KK_25519_ChaChaPoly_SHA256 (`Connection/Noise.lean`,
  checked against cacophony's vector). Its two messages are two
  conn-scope ops on the bare wire, `request` and `connection`, and the
  connection op's id is the connection id. A joiner's request rides in
  message 1's hello, so it reaches the inviter before any approval and
  opens nothing.
- **Local ops carry the secrets.** `eph` holds an ephemeral secret.
  `opened` is the responder's read of a request, citing this device's
  `secret`. `established` is each side's session: its validator re-runs
  that side's half of the handshake. A close purges them, which makes
  sessions forward secret (the purge branch).
- **Frames** (`Connection/Frame.lean`, not an op) are as poc-17's: the
  connection id, a random nonce, and XChaCha20-Poly1305 with the id as
  associated data. They carry no counters and need no replay tracking,
  because ops are idempotent.
- **In and out.** Every op taken gets a `recv` (when it arrived and
  how). Everything leaves through `send` couriers, which cite the op
  they carry and are read by reference when handed out.
- **One session per peer.** If two devices dial each other at once,
  both ends keep the session with the smaller connection id. They hold
  the same connection ops, so they agree without a message.
- **Closing purges two ops**, the connection and its request.
  Everything else of the session cites one of them (ephemerals, opened,
  established, couriers, arrivals), so purge takes it along.
- **Reactions** (`Connection/Intents.lean`). `react` opens, delivers,
  answers only peers the trust rule admits, and establishes. `dial`
  resends a pending join's request every tick. Both are views over lists
  returning ops, generic in the monad (`Lists`, `Store`, `Fresh`), so
  they run on SQLite and on the model.

Laws (`Connection/Laws.lean`, `Connection/Noise.lean`,
`Connection/Frame.lean`, `Engine/Families.lean`):
- `wire_kinds`;
- `established_agrees` (both ends hold one session);
- `handshake_agrees`, `sent1_write1`, `sent1_read1`, `read2_write2'`;
- `open_seal`, `cid_seal`;
- `sum_left`.

`Tests/ConnectionCheck.lean` runs two SQLite nodes through the node
driver: the join completes after approval, sync admits the joiner, and
posts flow. The join under heavy loss is pending purge.
