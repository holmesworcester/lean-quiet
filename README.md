# Lean Quiet

Quiet's engine, op families, apps and their proofs in Lean 4, in one
repository. Every part builds against the others at the same commit.

| directory | what |
|---|---|
| `engine/` | the op engine (store, judging, lists, sync, the node and its TCP runner), the Community and Connection families, the Rust crypto (`engine/native/crypto`) and their laws |
| `app/` | the Quiet app (`Quiet/`), its headless twin and tests, and its Android and iOS shells |
| `qr/` | QR encoding and decoding, and pictures (QOI) |
| `mdns/` | mDNS/DNS-SD discovery |
| `net/` | the connection bootstrap model and its laws |

Each directory is its own Lake package with its own `mise.toml` tasks.
CI runs locally for now: `ci/local.sh` runs every part's gate (or
`ci/local.sh engine app` for some), with logs in `out/ci/`;
`mise run check` here runs the same through each part's mise tasks.
`ci/workflow.yml` is the same for a hosted runner, not in use. The layout this repository
is moving to (engine for everything that holds for every op type; ops
by family and domain; platforms by name) is
[engine/docs/LAYOUT.md](engine/docs/LAYOUT.md); sync's design is
[engine/docs/SYNC.md](engine/docs/SYNC.md).

The history of each part is its former repository's (lean-engine,
lean-quiet, lean-qr, lean-mdns, lean-net), rewritten into its directory;
their other branches are kept as `import/<dir>/<branch>`.

## Proofs

148 laws, each checked by its part's `tests/check.sh` to rest on Lean's
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`): no
`sorry`, no added axiom. Engine 94, qr 23, app 17, net 11, mdns 3.

Significance:
- ★★★ is a guarantee a user or an attacker would care about.
- ★★ is a law the headline ones rest on.
- ★ is a supporting lemma.

Three assumptions stand outside the axioms, and each is stated where it is
used:
- signatures are unforgeable (`Unforgeable`);
- SHA-256 has no collision on what was hashed (`CollisionFree`, which
  gives `Distinct`);
- the SQLite store behaves like the model. That one is tested, not
  proven: row-for-row differential tests, and kill -9 crash tests.

### Membership and authority (`engine/Community`)

- ★★★ `no_impersonation`: a message attributed to user u and device d was
  signed, as that exact op, by the holder of d's key.
- ★★★ `admission_needs_approval`: nobody is admitted without a member's
  approval. The only exception is the founder, admitted by the root.
- ★★★ `admission_approved`: every admission is the founder's, or tallies
  a valid request with exactly its invitation's threshold of approvals by
  distinct users.
- ★★★ `request_invited`: nobody requests uninvited. A request redeems a
  valid invitation, and both the link's bearer key and the device signed
  it.
- ★★★ `removal_authorized`: only admins remove others, though anyone may
  remove themselves.
- ★★★ `removed_stays`: removal is permanent. No redelivery, delay or
  reordering undoes it.
- ★★★ `valid_stays`: removal does not rewrite history. Every valid fact
  stays valid as ops arrive.
- ★★★ `admin_removal_stands`, `mutual_removal`: every admin-issued removal
  stands, including two admins removing each other.
- ★★ `message_authorized`, `approval_signed`, `invitation_issued`,
  `admission_consented`, `admin_granted`, `named_by_admin`: each kind of
  op was signed by whom it must be.
- ★★ `admit_admits`, `request_valid`, `approve_valid`,
  `removed_approver_admits`: these say the honest path works, and that a
  removed member's earlier approval still counts.

### Who a node connects to, and seals keys to (`engine/Community/Connect`)

- ★★★ `connect_iff`, `connect_approved`, `refuse_nonmember`: at rest, a
  node accepts exactly the devices of users that are admitted and not
  removed. That means the founder, or devices approved to the threshold;
  never an outsider or a removed member.
- ★★★ `removal_cuts_off`: a removal, once held, cuts off every device of
  the removed user (unless it is admitted into another live user).
- ★★★ `recipients_iff`: a content key is sealed to exactly the live
  members' devices, with no outsider, no removed device, and no member
  left out.
- ★★★ `connect_agree`: nodes that hold the same ops agree on whom to
  connect to.
- ★★ `connect_admitted`, `members_iff`, `removals_iff`.

### The engine: ids, judging, storage (`engine/Engine`)

- ★★★ `Op.id_decode`, `distinct_of_collisionFree`: an op is named by the
  hash of the bytes received, whoever sent them, so a peer cannot give
  an op a name.
- ★★★ `same_ops_same_verdicts`, `order_free`: two nodes that received
  the same ops, in any order, batching or interleaving, finish with the
  same verdicts.
- ★★★ `drain_terminates`, `drain_settles`, `drain_bounded`: judging
  terminates, within the budget the writer reads off its tables, and
  then every verdict is the spec's. There is no `partial` loop in the
  write path.
- ★★ `Codec.encode_decode`, `Codec.decode_encode`, `Op.decode_bytes`:
  decoding is strict, and round-trips, so a value has one byte string.
- ★★ `status_iff_spec`, `spec_extends`, `inv_ingest`, `inv_step`,
  `step_budget`: stored verdicts are the spec's, and once reached they
  never change.
- ★ `reach_drain`, `run_step`, `run_drain`, `reach_ops`.

### Lists and live reads (`engine/Engine/View`, `Decl`)

- ★★★ `eval_stable`, `view_stable`: a list, or any view built from lists,
  changes only when a row is filed under a key it read. That is why a
  screen re-reads only what changed.
- ★★ `filed_rel`, `mem_keysOf`: a relation lists exactly its valid facts.
- ★ `View.run_model`, `Rel.key_ne_opKey`, `rels_distinct`.

### Sync (`engine/Engine/Sync*`)

- ★★★ `exchange_complete`: one RBSR round, made of the two sides' real
  `answer` composed, sends each side exactly what the other holds in the
  range and it lacks, within |X∩r|+|Y∩r|+1 answers on any path.
  Applied to window ranges, this is completeness for a windowed node.
- ★★★ `recv_take`, `recv_send`: a connection hands the store only shared
  ops in rooms the peer may see. It sends only sync messages and ops in
  its rooms, so asking for another room's op by id gets nothing.
- ★★★ `spec_local` (locality): holding an op's requirement closure is
  enough to reach the peer's verdict on it.
- ★★★ `intake_local`, `stored_local`: a peer can push no local op in, so
  every local op a node stores is its own.
- ★★ `lbl_inj`: equal Merkle labels mean equal sets, given no collision.
- ★★ `offer_shared`, `offer_stored`, `filed_send`, `tick_send`,
  `intakeConn_conn`, `opening_honest`.
- ★ `num_inj`.

### Connections and purge (`engine/Connection`, `Engine/Purge`)

- ★★★ `handshake_agrees`: an honest Noise handshake agrees. Both sides
  derive the same keys, and each reads what the other wrote.
- ★★★ `established_agrees`: both ends of a connection hold one session.
- ★★★ `wire_kinds`: only the two handshake messages cross the bare wire.
- ★★★ `open_seal`, `cid_seal`: a frame opens to what was sealed under the
  matching key, and names the connection it was sealed for.
- ★★★ `purge_gone`, `purge_shared`, `purge_settles`: a purged op (a
  session's secrets, a courier) is gone, and no shared op is ever
  deleted. The engine then settles on what remains.
- ★★ `purge_named`, `purge_undecides`, `purge_inv`, `mem_purgeSet`,
  `local_kinds`, `sent1_write1`, `sent1_read1`, `read2_write2'`.
- ★★ `sum_left`, `sum_scope_left`: composing families leaves the first
  family's verdicts and scopes unchanged.

### Device state and intents (`engine/Community`)

- ★★★ `local_fact_mine`: a device's own state (secrets, acceptances,
  pending joins) is its own. No peer can create it.
- ★★★ `join_travels`, `found_travels`, `stopWaiting_local`: of the ops an
  intent writes, only the shared ones (the request, the community's)
  ever leave the device.
- ★★ `secret_derives`: a stored secret's seed derives its public key.
- ★★ `parse_text`, `parse_valid`, `Base62.decode_encode`: an invite
  link's text parses back to the link, and whatever parses is valid.

### Bootstrap (`net/`)

These laws are over a model of the protocol rules and a two-node scene,
not yet over the running node; see the wanted list below.

- ★★★ `no_connection_before_approval`: a request opens nothing. Until
  approval, however hellos are lost, duplicated or reordered, neither
  side has a session.
- ★★★ `bootstrap`: over a failing socket, in every fair run, the joiner
  eventually connects and both hold the same ops.
- ★★★ `sessions_trusted`: sessions only form with peers trusted by the
  node's own ops.
- ★★ `bootstrap_possible`, `bootstrap_ideal`, `reachable_inv`,
  `allowPeer_iff`, `allowPeer_settles`.
- ★ `admitted_inv`, `allowedA`, `allowedB`.

### The app's screen (`app/Quiet`)

- ★★★ `visible_in_viewport`: nothing on screen is covered. Content in the
  viewport lands below the header and above the composer and keyboard.
- ★★★ `hit_iff`, `pinned_tap`: what you tap is what is drawn there,
  keyboard open or not.
- ★★★ `newest_visible`: pinned to the bottom, the newest message is
  wholly visible.
- ★★ `placed_row`, `newest_drawn`, `pinned_row`, `pinned_visible`: the
  slide and keyboard shift are exact, and the keyboard covers a page
  without pushing it.
- ★★ `keys_disjoint`, `hit_cell`, `reachable`, `compose_row`,
  `compose_top`: in the emoji sheet, keys never overlap, every key is
  reachable, and the grid shows exactly its scrolled content.
- ★★ `Link.hints_fit`, `Link.qr_fits`: an invite's hints and QR fit.
- ★ `clamp_le`, `Camera.src_in`.

### QR codes and pictures (`qr/`)

- ★★★ `parse_valid`, `parse_segsBits`, `parse_dataStream`: what the
  decoder returns is valid, and what the encoder writes reads back.
- ★★★ `decodeImage_malformed`, `decode_sized`: hostile input is safe. A
  malformed image or QOI decodes to a well-formed result or nothing.
- ★★ `RS.correct_sound`, `RS.correct_clean`, `decodeFormat_correct`,
  `decodeVersion_correct`: error correction is sound, and the format and
  version readings tolerate their designed number of bit errors.
- ★★ `render_opaque`, `render_wellFormed`, `scale_wellFormed`.
- ★ `readBits_bitsOf`, `bytesBits_packBytes`, `fit_*`, `layout_*`,
  `add_stored`.

### Discovery (`mdns/`)

- ★★ `decode_encode`, `decode_valid`, `decode_roundtrip`: a valid mDNS
  message survives the wire, and whatever the decoder accepts is valid.

### Wanted

Sync and connections:
- [ ] ★★★ `conn_runs_exchange`: the connection code, over any delivery
  order, performs `exchange`. This lifts `exchange_complete` from the
  round to the running connection.
- [ ] ★★★ `closure_delivered`: after an op and its offers are answered,
  the peer holds the op's requirement closure. With `spec_local`, a
  windowed node then judges everything it holds as its peer does.
- [ ] ★★★ `have_shown`: every id a connection offers names a stored op in
  one of its rooms. The disclosure law for ids, which needs the room
  index's invariant.
- [ ] ★★ efficiency bounds: each op is sent at most once per connection
  and each id offered once. A round needs at most fan·|Δ|·⌈log n⌉ claims
  and 2+2⌈log_fan n⌉ messages per path.
- [ ] ★★ the cached Merkle treap: its labels are `lbl`'s (unique
  canonical tree, insert, clamp), for O(log n) fingerprints with no
  change on the wire.
- [ ] ★★ `exchange_complete` for stores that grow during a round, which
  sync-as-ops needs.

The running system end to end:
- [ ] ★★★ the two-node world over the real node and families: no
  connection before approval, bootstrap under fair loss, and
  convergence, proved over the code that runs. This retires `net/`'s
  separate model.
- [ ] ★★★ network to pixel, per domain: after a fair sync, the device
  shows the row whose pixels are its view of the fact. One pipeline
  theorem, plus each domain's own obligations.
- [ ] ★★★ `page_sync`: after syncing a page, a device shows every row its
  peer shows for that page.
- [ ] ★★ the screen: no blank rows within a latency bound, a frame
  budget, bounded reads, and flow control for one-shot watches.

Security beyond what is built:
- [ ] ★★★ handshake authentication and secrecy: only the two devices
  derive a session's keys (under the usual cryptographic assumptions).
- [ ] ★★★ forward secrecy at rest: after a session's purge with scrub,
  its keys cannot be recovered from storage.
- [ ] ★★★ key rotation after removal: removed devices cannot read later
  messages (rotation is not built yet).
- [ ] ★★ vouching, channels and deletion (not built yet).

Display order (follow-up design, `engine/docs/SYNC.md`):
- [ ] ★★ `display_agrees`, `display_local`, `exception_real`,
  `reply_below`: two devices with the same ops order messages alike,
  except the saturated tail, which follows each device's receipt order.
