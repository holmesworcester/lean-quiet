# Lean Quiet

Quiet's engine, op families, apps and their proofs in Lean 4, in one
repository. Every part builds against the others at the same commit.

## What is proven

Lean checks these theorems about the code that runs. Whatever any peer
or anyone on the network does:

- **nobody can post as another member;**
- **nobody joins without an invitation and members' approval;**
- **only admins remove others, and no removal can be undone;**
- **non-members get none of a community's ops, and no device's secrets
  leave it;**
- **a node's trust rule lets in exactly the live members, and honest
  nodes that hold the same ops agree.**

**Not yet proven:** that sessions and messages are secret from someone
on the wire, which takes cryptographic proofs, and the bootstrap over
the running code rather than a model.

How to read it:
- **The attacker** is any peer, a removed member included, or anyone on
  the network. It sends any bytes, and replays, delays, reorders or
  drops any message. It cannot break the cryptography, or control a
  member's device.
- **Each theorem is about the functions that run** in the app and the
  daemon, over the engine's own store. The SQLite store is tested
  against that store row for row, not proven. *(model)* marks a theorem
  about a separate model instead.
- **All 148 rest on Lean's standard axioms only:** no `sorry`, no added
  axiom (each part's `tests/Axioms.lean`).
- **Where a theorem says so, it assumes** that Ed25519 signatures cannot
  be forged, that SHA-256 has no collisions, and that the AEAD and
  X25519 work as specified.

✅ proven · 🟡 partly · ⬜ wanted

### Against an attacker

| | Guarantee | Theorems |
|---|---|---|
| | **Identity and membership** | |
| ✅ | **No impersonation.** A message attributed to user u's device d was signed, as that exact op, by d's key. That key also signed d's admission into u. | `no_impersonation` |
| ✅ | **No joining unapproved.** Every member is the founder, or redeemed an invitation and was approved by its threshold of distinct members. The request was signed by both the link's key and the device. | `admission_needs_approval`, `admission_approved`, `request_invited` |
| ✅ | **Only admins remove others,** and only admins make admins. | `removal_authorized`, `admin_granted` |
| ✅ | **Removal sticks, and history stays.** No replay, delay or reordering restores a removed member, or invalidates a valid op. | `removed_stays`, `valid_stays` |
| ✅ | **Ops cannot be misnamed.** An op's id is the SHA-256 of the bytes received, whoever sent them, and decoding is strict. | `Op.id_decode`, `distinct_of_collisionFree` |
| | **Confidentiality** | |
| ✅ | **Non-members get no ops, even by asking by id.** A session sends only sync messages, and ops of the rooms its peer is let into. | `recv_send` |
| ✅ | **Secrets stay on the device.** No local op (a secret, a session key, a pending join) is ever offered or sent. Of a connection's ops, only the two handshake messages are not local. | `recv_send`, `offer_shared`, `wire_kinds`, `join_travels` |
| 🟡 | **Messages are sealed to members only.** Proven: a content key goes to exactly the live members' devices. In progress: sealing posts with it. | `recipients_iff` |
| ⬜ | **Sessions are secret and authenticated:** only the two devices can derive a session's keys. Proven so far: an honest handshake agrees. | `handshake_agrees` |
| ⬜ | **Removed members cannot read new messages.** This needs key rotation, which is not built. | |
| ⬜ | **A closed session's keys cannot be recovered from disk.** Proven so far: their rows are gone. | `purge_gone` |
| | **Connections** | |
| ✅ | **The trust rule lets in exactly the live members.** Read from the node's tables, it accepts exactly the devices of admitted, unremoved users. A removal cuts off all of that user's devices. | `connect_iff`, `refuse_nonmember`, `removal_cuts_off` |
| 🟡 | **No session before approval,** however hellos are lost or replayed, and sessions form only with trusted peers. Proven over a model; wanted over the running handshake. | `no_connection_before_approval`, `sessions_trusted` *(model)* |
| ✅ | **Peers cannot push ops in** outside the rooms they are let into, nor plant a device's local state. | `recv_take`, `intake_local`, `stored_local`, `local_fact_mine` |
| ✅ | **Both ends hold one session.** Two ends that complete a handshake hold the same hash, each names the other, and each one's send key is the other's receive key. A frame opens to what was sealed, for the connection it names. | `established_agrees`, `open_seal`, `cid_seal` |
| | **Hostile input** | |
| ✅ | **Judging cannot be hung.** From any state, judging empties its queue within a budget read off the tables. | `drain_bounded`, `drain_terminates` |
| ✅ | **Hostile bytes decode to a well-formed value or to nothing.** This holds for ops (strictly), QOI pictures (1–2048 px a side), mDNS packets and invite links. | `Codec.encode_decode`, `Pic.decode_sized`, `Mdns.decode_valid`, `parse_valid` |
| ⬜ | **Resources are capped:** memory, rounds and frames per peer. | |

### Correctness

| | Guarantee | Theorems |
|---|---|---|
| ✅ | **Honest nodes agree.** The same ops, in any order, batching or interleaving, give the same verdicts. | `same_ops_same_verdicts`, `order_free` |
| ✅ | **A sync round is complete.** Each side is sent exactly what the other holds in the range and it lacks. On any path, it takes at most one answer more than the two sides hold in the range. | `exchange_complete` |
| ✅ | **Partial sync is safe.** A node that holds an op's requirement closure judges it as its peer does. | `spec_local` |
| ✅ | **Purge is safe.** A purged session or courier is gone, no shared op is ever deleted, and the engine settles on what remains. | `purge_gone`, `purge_shared`, `purge_settles` |
| ✅ | **A screen re-reads only what changed.** A list changes only when a row is filed under a key it read. | `eval_stable`, `view_stable` |
| ✅ | **Nothing on screen is covered or mis-tapped.** Content in the viewport is drawn below the header, and above the composer and keyboard. A tap lands on the row, or emoji key, drawn under it. | `visible_in_viewport`, `pinned_tap`, `hit_iff` |
| 🟡 | **A joiner connects, and both sides converge,** over a socket that loses, duplicates and reorders. Proven over a model only. | `bootstrap` *(model)* |
| ⬜ | **The running connection does all this.** It performs the round, and delivers each op's requirement closure. | `conn_runs_exchange`, `closure_delivered` |
| ⬜ | **What you see is what was sent.** The device draws the rows of the facts its ops hold, from network to pixel. | |

### Every theorem

🥊🥊🥊 a guarantee above · 🥊🥊 a law those rest on · 🥊 a lemma.
Each theorem's docstring states it.

- **Engine core** (`engine/Engine`). 🥊🥊🥊 `same_ops_same_verdicts` `drain_bounded` `drain_terminates`. 🥊🥊 `order_free` `drain_settles` `status_iff_spec` `spec_extends` `inv_ingest` `inv_step` `step_budget`. 🥊 `reach_drain` `run_step` `run_drain` `reach_ops`.
- **Ops on the wire.** 🥊🥊🥊 `Op.id_decode` `distinct_of_collisionFree` `Codec.encode_decode`. 🥊🥊 `Codec.decode_encode` `Op.decode_bytes`.
- **Purge.** 🥊🥊🥊 `purge_gone` `purge_shared` `purge_settles`. 🥊🥊 `purge_named` `purge_undecides` `purge_inv`. 🥊 `mem_purgeSet`.
- **Lists and views.** 🥊🥊🥊 `eval_stable` `view_stable`. 🥊🥊 `filed_rel` `mem_keysOf` `sum_left` `sum_scope_left`. 🥊 `View.run_model` `Rel.key_ne_opKey`.
- **Sync** (`engine/Engine/Sync`). 🥊🥊🥊 `exchange_complete` `spec_local` `recv_send` `recv_take` `intake_local` `stored_local` `offer_shared`. 🥊🥊 `lbl_inj` `offer_stored` `filed_send` `tick_send` `intakeConn_conn` `opening_honest`. 🥊 `num_inj`.
- **Membership** (`engine/Community`). 🥊🥊🥊 `no_impersonation` `admission_needs_approval` `admission_approved` `request_invited` `removal_authorized` `admin_granted` `removed_stays` `valid_stays`. 🥊🥊 `admin_removal_stands` `mutual_removal` `message_authorized` `approval_signed` `invitation_issued` `admission_consented` `named_by_admin` `admit_admits` `request_valid` `approve_valid` `removed_approver_admits`.
- **Whom to connect and seal to** (`engine/Community/Connect.lean`). 🥊🥊🥊 `connect_iff` `refuse_nonmember` `removal_cuts_off` `recipients_iff`. 🥊🥊 `connect_approved` `connect_admitted` `connect_agree` `members_iff` `removals_iff`. 🥊 `rels_distinct`.
- **Device state and links.** 🥊🥊🥊 `local_fact_mine` `join_travels` `parse_valid`. 🥊🥊 `found_travels` `stopWaiting_local` `secret_derives` `parse_text`. 🥊 `Base62.decode_encode`.
- **Connection** (`engine/Connection`). 🥊🥊🥊 `established_agrees` `wire_kinds` `open_seal` `cid_seal`. 🥊🥊 `handshake_agrees` `sent1_write1` `sent1_read1` `read2_write2'`. 🥊 `local_kinds`.
- **Bootstrap** (`net/`, *model*). 🥊🥊🥊 `no_connection_before_approval` `sessions_trusted` `bootstrap`. 🥊🥊 `bootstrap_possible` `bootstrap_ideal` `reachable_inv` `allowPeer_iff` `allowPeer_settles`. 🥊 `admitted_inv` `allowedA` `allowedB`.
- **Discovery** (`mdns/`). 🥊🥊🥊 `Mdns.decode_valid`. 🥊🥊 `Mdns.decode_encode` `decode_roundtrip`.
- **QR codes and pictures** (`qr/`). 🥊🥊🥊 `Pic.decode_sized`. 🥊🥊 `Qr.parse_valid` `parse_segsBits` `parse_dataStream` `RS.correct_sound` `RS.correct_clean` `decodeFormat_correct` `decodeVersion_correct` `render_opaque` `render_wellFormed` `scale_wellFormed`. 🥊 `decodeImage_malformed` `readBits_bitsOf` `bytesBits_packBytes` `fit_small` `fit_le` `fit_pos` `fit_long` `fit_round` `layout_sizes` `layout_inside` `layout_apart` `add_stored`.
- **The screen** (`app/Quiet`). 🥊🥊🥊 `visible_in_viewport` `pinned_tap` `hit_iff`. 🥊🥊 `newest_visible` `newest_drawn` `placed_row` `pinned_row` `pinned_visible` `keys_disjoint` `hit_cell` `reachable` `compose_row` `compose_top` `Link.hints_fit` `Link.qr_fits`. 🥊 `clamp_le` `Camera.src_in`.

### Also wanted

- [ ] 🥊🥊🥊 **The two-node world over the running code:** no session before approval, bootstrap under fair loss, and convergence, proven of the node and families that run. This retires `net/`'s model.
- [ ] 🥊🥊🥊 **`have_shown`:** every id a connection offers names a stored op in one of its rooms. This is the disclosure law for ids.
- [ ] 🥊🥊🥊 **`page_sync`:** after syncing a page, a device shows every row its peer shows for that page.
- [ ] 🥊🥊 **Efficiency.** Each op is sent at most once per connection. A round needs at most fan·Δ·⌈log n⌉ claims.
- [ ] 🥊🥊 **The cached Merkle tree's labels are `lbl`'s,** for O(log n) fingerprints with no change on the wire.
- [ ] 🥊🥊 **The screen keeps up:** no blank rows past a latency bound, a frame budget, and bounded reads.
- [ ] 🥊🥊 **Display order** (design in `engine/docs/SYNC.md`). Devices with the same ops order messages alike, except a saturated tail, which follows receipt order.
- [ ] 🥊🥊 **Laws for features not built yet:** vouching, channels and deletion.

## Layout

| directory | what |
|---|---|
| `engine/` | the op engine (store, judging, lists, sync, the node and its TCP runner), the Community and Connection families, the Rust crypto (`engine/native/crypto`) and their laws |
| `app/` | the Quiet app (`Quiet/`), its headless twin and tests, and its Android and iOS shells |
| `qr/` | QR encoding and decoding, and pictures (QOI) |
| `mdns/` | mDNS/DNS-SD discovery |
| `net/` | the connection bootstrap model and its laws |

Each directory is its own Lake package, with its own `mise.toml` tasks.

CI runs locally for now:
- `ci/local.sh` runs every part's gate, or `ci/local.sh engine app` for
  some. Logs go to `out/ci/`.
- `mise run check` here runs the same through each part's mise tasks.
- `ci/workflow.yml` is the same for a hosted runner, and is not in use.

The layout this repository is moving to is
[engine/docs/LAYOUT.md](engine/docs/LAYOUT.md): the engine for
everything that holds for every op type, ops by family and domain, and
platforms by name. Sync's design is
[engine/docs/SYNC.md](engine/docs/SYNC.md).

Each part's history is its former repository's (lean-engine,
lean-quiet, lean-qr, lean-mdns, lean-net), rewritten into its directory.
Their other branches are kept as `import/<dir>/<branch>`.
