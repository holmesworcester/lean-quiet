# lean-engine

A persisted op engine in Lean 4, with libquiet's validity model, a
community family on top, and proofs that reach from SQLite rows to
high-level guarantees about membership, removal, impersonation,
connection and sealing. A first pass: deletion, vouching, channels,
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
- `order_free`: two nodes that received the same ops, in any order and
  batching, hold the same verdicts at rest.
- `spec_extends`: a verdict, once reached, never changes.
- `Codec.decode_encode`: what SQLite stores decodes to what was written.

## The community (`Community/`)

Root (founder, admin), invite, join (member or linked device), admin
grant, removal, post, wrap — after libquiet's DESIGN.md and its removal
stack (#778, #98, #1088). Validity reads only cited facts, so every
admin-issued removal stands: of other admins, mutually, and by an admin
who has since been removed. Removal never invalidates an op; it changes
who counts.

Laws (`Laws.lean`, `Connect.lean`):

| question | law |
|---|---|
| Are all messages by admitted users? | `message_authorized` |
| Is impersonation impossible? | `no_impersonation` (given unforgeable signatures), `admission_consented` |
| Can outsiders join? | `admission_invited`, `invitation_issued` |
| Are linked devices and invited members admitted? | `join_admits` |
| Who may remove whom? | `removal_authorized`, `admin_removal_stands`, `mutual_removal`, `admin_granted` |
| Can a removal be undone, or rewrite history? | `removed_stays`, `valid_stays` |
| Do we connect to non-members or removed members? | `connect_iff`, `refuse_nonmember` |
| Do we connect to linked devices and invited members? | `connect_joined` |
| Who is a new content key sealed to? | `recipients_iff` |

The connection and sealing laws are about the queries themselves
(`allowPeer`, `recipients`) run on the persisted tables.

## What is assumed, not proven

- SQLite behaves like the model (untampered, atomic). Tested:
  `differential` compares every table row for row under random
  workloads and schedules; `crash` kills the writer with SIGKILL and
  checks the disk holds whole batches.
- Signatures are unforgeable (`Unforgeable`, a hypothesis where used).
  Ed25519 is libsodium's at runtime.
- Op ids do not collide (`Distinct`).
- Judging terminates (the runtime loops until the queue is empty).
- Confidentiality is proven as "who keys are sealed to", not as a
  cryptographic property, and removed users keep keys they already
  hold: no rotation yet, as in libquiet's current increment.

## Running

    mise run check   # build proofs, audit axioms (standard only)
    mise run test    # scenario, differential, crash

Needs `ELAN_HOME` with Lean 4.34.0, and SQLite and libsodium (headers
for SQLite). The CI workflow runs both tasks; this repo has no remote
yet.
