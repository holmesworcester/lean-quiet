# Lean Quiet

[Lean](https://lean-lang.org) is usually for proving statements with and about code. But can we 
build entire apps with it, and prove they work as users might want?
I think we can now!

This app is written mostly in Lean. It builds for iOS and Android and implements chat with emojis and reactions. Non-Lean code is limited to things like scrolling or using the camera ([what isn't Lean, and why](#what-isnt-lean-and-why)) so in a
meaningful sense Lean does everything from processing TCP packets to drawing pixels on the screen.
This allows for proving a surprising range of user-relevant properties! See: [What is Proven](#what-is-proven).

Like [Quiet](https://github.com/TryQuiet/quiet), Lean Quiet is also local-first, end-to-end encrypted, and peer-to-peer, so many properties that would normally depend on a server operator (such as privacy, access control, or uptime) are provided by the code itself. This means they are provable over all possible deployments, assuming user device integrity! See: [Towards Proofs for n Clients](#towards-proofs-for-n-clients).

Can we also prove the absence of the *qualitative* bugs that only show up in certain cases, like UI layout glitches at a certain screen size or RTL language, or a lack of responsiveness under load, or an accessibility gap? This seems tantalizingly possible too, and we show many such proofs here.

There is something exhilarating about adding a proof where one would usually add an end-to-end test. Sci fi. 🪐 

# What it looks like

<p align="center"><img src="docs/media/android-demo.webp" width="300" alt="Lean Quiet on Android: a message, Hebrew, Arabic and mixed scripts, a heart reaction, a photo, then flings through 1,000 messages"></p>

<p align="center"><em>The status bar and keyboard are Android's, the rest is Lean. Scrolling is better in person.</em></p>

## What is proven

Lean checks these theorems about the code that runs, except the one
marked *(model)*, which is over a model so far. Whatever any peer or
anyone on the network does:

- **nobody can post as another member;** ¹
- **nobody joins without an invitation and members' approval;** ¹
- **only admins remove others, and no removal can be undone;** ¹
- **no peer can alter or rename an op:** its id is the hash of its
  bytes, and it has one parse; ²
- **non-members get none of a community's ops;**
- **no device's secrets leave it;**
- **a node's trust rule lets in exactly the live members;** ¹
- **honest nodes that hold the same ops agree;** ² *(model)*
- **only a session's two nodes can derive its keys, even if both
  nodes' long-term keys later leak.** ³

¹ assuming Ed25519 signatures cannot be forged. ² assuming SHA-256 has
no collisions. ³ in the symbolic model of the cryptography.

**Not yet proven:**
- that messages are secret from non-members (the seal's secrecy);
- that every connection step reads its rooms afresh, so that a removal
  reaches a live session (tested, not proven);
- the bootstrap over the running code, rather than a model;
- that content is drawn faithfully all the way to pixels (proven up to
  each row's layout; painting is not).

### Towards Proofs for n Clients

The sync proofs already run the real sync code, in a world of two
devices whose network can delay, reorder or drop messages
([`stream_delivers`]). Devices that hold the same ops agree, whatever
order the ops arrived in (proven so far over a model of purging:
[`same_ops_same_verdicts`]). So for n devices, it comes down to proving
that every op reaches every member: the running round under any
delivery order (`conn_runs_exchange`) and the closure it delivers
(`closure_delivered`), then a world of n devices with fair delivery.

### What is Assumed

**Hypotheses.** These are named in the theorems that take them, and
nothing else is assumed:
- [`Unforgeable`]: a signature that verifies under a device key was made
  by that key's holder (Ed25519).
  - The membership theorems say "signed by d" to mean "the signature
    verifies under d".
  - `no_impersonation` takes `Unforgeable` to conclude that d's holder
    signed.
  - Reading any of them as "an attacker cannot" rests on it.
- [`CollisionFree`]: SHA-256 has no collision among the ops a node
  received.
  - It gives [`Distinct`]: no two ops share an id.
  - The engine's agreement and budget theorems take `Distinct`.
  - Sync's Merkle labels take the same of what they hash (in
    [`lbl_inj`]).
- [`NoSecondPreimage`]: SHA-256 has no second preimage on a file's
  Merkle tree inputs, for the attachment laws. [`assumptions_hold`]
  shows that it can hold.
- [`Suite.Good`]: X25519 agrees (`dh a (pub b) = dh b (pub a)`), the
  AEAD opens what it seals, and public keys are 32 bytes. These are
  correctness only, and say nothing about secrecy.
- **A read transaction is one moment** (`read_one_moment` and
  `agrees_notice` take it), as two hypotheses. *Snapshot:* inside one
  SQLite read transaction, every read answers as one state of the store
  and outbox (SQLite's snapshot isolation, on a WAL reader). *Journal:*
  the rows and verdicts a notice takes (the journal's, written by
  triggers on the index and verdict tables, netted, and a write's own
  ops' positions), matched against the windows the cache watches, reach
  every read whose answer changed since the last moment. Over the
  engine's model that is a theorem (`read_notice_iff`, `watch_stable`),
  and `window_check` tests the triggers against it. The headless app's
  `liveSound` check tests the journal (every fresh answer the cache
  holds equals a read now); the snapshot is not tested on its own.
- **The session secrecy theorems assume the symbolic (Dolev-Yao)
  model:** perfect primitives, with the attacker reading, replaying and
  injecting every message. They have no computational reduction. DH is
  over named exponents only, with no low-order points, clamping or
  Ed25519-to-X25519 conversion. Their agreement is non-injective: a
  replayed handshake is accepted again.

**Trusted, not proven.** Each item is tested instead, as noted:
- **Lean** (its kernel, compiler and runtime), and the OS's randomness
  for keys and nonces.
- **The crypto libraries meet those hypotheses:** ed25519-dalek,
  curve25519-dalek, chacha20poly1305 and sha2, the Rust crates libquiet
  uses. They are tested byte-identical to libsodium, and the handshake
  is tested against the Noise test vectors.
- **SQLite behaves like the engine's own store.** This is tested row for
  row against the model, and with kill -9 crash tests. A frame's reads in one
  transaction see one committed state (SQLite's snapshot isolation): the
  snapshot hypothesis above, which the screen's laws take.
- **Deleted bytes are gone from the disk.**
  - A purge deletes with SQLite's `secure_delete` on, then runs
    `VACUUM` and truncates the WAL.
  - `tests/engine/Purge.lean` reads the database's files raw and finds no
    byte of a purged secret.
  - Without any one of the three steps, it does find them.
  - Below SQLite, it is assumed that the filesystem and the flash keep
    no older copy of a block.
  - In practice that is doubtful: journaling and copy-on-write
    filesystems, and flash wear-levelling, keep old blocks.
  - The sound fix is for session secrets never to reach the disk, as
    ephemeral ops (wanted, below).
- [**The native code**](#what-isnt-lean-and-why): what connects Lean to
  the OS, and the libraries it calls. It is tested end to end, over
  localhost TCP and on devices.
- **That each statement says what we mean.** Read it: every name below
  links to its statement.

### Security proofs

✅ proven over running code · 🟡 partly · ⬜ wanted · *(model)* proven
over a separate model. 🥊🥊🥊 is what a user is promised; 🥊🥊 is what
that rests on; 🥊 is supporting. All 993 rest on Lean's standard axioms
only, and about three quarters of its theorems (751 of 973, not counting 20 negative controls) are about the code that runs; another 10 run the
phone's node code over a modelled network and plain transport (the
World); the rest are over models so far
([not yet about running code](#not-yet-about-running-code-todo)).

| | | Guarantee | Theorems |
|---|---|---|---|
| | | **Identity and membership** | |
| ✅ | 🥊🥊🥊 | **No impersonation.** A message attributed to user u's device d was signed, as that exact op, by d's key. That key also signed d's admission into u. | [`no_impersonation`] |
| ✅ | 🥊🥊🥊 | **No joining unapproved.** Every member is the founder, or redeemed an invitation and was approved by its threshold of distinct members. The request was signed by both the link's key and the device. | [`admission_needs_approval`], [`admission_approved`], [`request_invited`] |
| ✅ | 🥊🥊🥊 | **Only admins remove others,** and only admins make admins. | [`removal_authorized`], [`admin_granted`] |
| ✅ | 🥊🥊🥊 | **Removal sticks, and history stays.** No replay, delay or reordering restores a removed member, or invalidates a valid op. | [`removed_stays`], [`valid_stays`] |
| ✅ | 🥊🥊 | **Every op is signed by whom it must be.** A message is signed by an admitted device of its author, and an approval by a member other than the requester. An invitation is signed by its issuer, and a community's name by an admin. Each admission was consented to by its device. | [`message_authorized`], [`approval_signed`], [`invitation_issued`], [`named_by_admin`], [`admission_consented`] |
| ✅ | 🥊🥊 | **Admins' removals stand,** even of each other, and a removed member's earlier approvals still count. | [`admin_removal_stands`], [`mutual_removal`], [`removed_approver_admits`] |
| | | **Confidentiality** | |
| ✅ | 🥊🥊🥊 | **Non-members get no ops, even by asking by id.** A session sends only sync messages and ops of the rooms its peer is let into. A have for a room the peer may not see is ignored, so a peer cannot ask whether this node holds an op of another community, or a local op. Wants authorize ids against the shown rooms' index before any blob read. | [`recv_send`], [`hold_reply_local`], [`heldIn_index`], [`hold_reply_local_premises`], [`onWant_authorized`], [`serveOwed_blind`], [`serveOwed_shown`] |
| ✅ | 🥊🥊🥊 | **Secrets stay on the device.** The running filed and closure offers name only shared ops; no local op (a secret, a session key, a pending join) is offered or sent. Of a connection's ops, only the two handshake messages are not local. | [`offer_shared`], [`wire_kinds`], [`local_kinds`], [`joinOps_travels`], [`found_travels`], [`stopWaiting_local`] |
| ✅ | 🥊🥊 | **The stream discloses only what it may.** The running filed stream and closure walk offer only stored, shared ops in shown rooms. `Conn.tick` sends only round messages, offers and retries. | [`filed_send`], [`offer_shared`], [`offer_stored`], [`tick_send`] |
| 🟡 | 🥊🥊🥊 | **Messages are sealed to members only.** Proven: the `recipients` query names exactly the node keys of live members' devices, and a member opens what was sealed under the key wrapped to it. Not yet: the running wrap writers use that query (today an approval below its threshold already wraps the key to the requester), and the seal's secrecy from non-members. | [`recipients_iff`], [`members_iff`], [`member_opens`], [`openSealed_seal`], [`unbox_box`], [`check_reads_shared`] |
| ✅ | 🥊🥊🥊 | **Sessions are secret and authenticated,** in the symbolic model, over the handshake functions that run. An attacker who reads, replays and injects every message, and knows every key but the two nodes' static keys and the session's ephemerals, derives neither transport key, and the initiator accepts only the reply the responder wrote to this request. Replays are accepted again; payloads are not covered. | [`kk_secret`], [`kk_secret_init`], [`kk_secret_resp`], [`kk_authentic`], [`kk_authentic_resp`], [`kk_secret_init_tight`], [`kk_runs`], [`handshake_agrees`] |
| 🟡 | 🥊🥊🥊 | **A closed session's keys cannot be recovered,** from the disk or from the static keys later. Every way a session ends purges its keys, and a silent session ends after `live` (90 s by default). With the ephemerals gone, the transcript and both static keys do not give the transport keys (tested: no file of the database keeps a byte of them). Not yet: that `closing` names every ephemeral (`close_forgets`). | [`close_purges`], [`close_gone`], [`drop_iff_silent`], [`keepalive_sent`], [`live_stays`], [`kk_forward_secret`], [`purge_named`] |
| ⬜ | 🥊🥊🥊 | **Session secrets never reach the disk.** They would be ephemeral ops, held in memory, so forward secrecy would not rest on deletion. A restart then redials. | |
| ⬜ | 🥊🥊🥊 | **Removed members cannot read new messages.** This needs key rotation, which is not built. | |
| 🟡 | 🥊🥊 | **Every offered id names a stored op in one of the peer's rooms.** Proven of each step a connection takes, while the room index holds exactly each room's stored ops; booting, write turns and purges keep it so. Not yet: that the node's entry points (`onFrame`, `onTick`, `onWrite`) chain these steps. | [`have_shown`], [`boot_cached`], [`write_cached`], [`purge_cached`], [`cached_items`], [`write_snaps`], [`have_shown_premises`] |
| | | **Connections** | |
| ✅ | 🥊🥊🥊 | **A node handshakes with its own key, not a device's.** Proven: a session's statics are the two nodes' keys, each held as a local op, and device keys only sign. The binding is the device's own consent: the root or request that admitted it carries its node's key under its signature. So a removed device does not block a new device on the same node. | [`opened_endpoint`], [`established_endpoint`], [`endpoint_signed`], [`endpoint_derives`], [`meV_node`], [`new_device_trusted`] |
| ✅ | 🥊🥊🥊 | **The trust rule lets in exactly the live members' nodes.** Read from the node's tables, it accepts a node key exactly when a live device is admitted under it: admitted, and none of its users removed. Nodes that hold the same ops agree on it. | [`connect_iff`], [`deviceLive_iff`], [`refuse_nonmember`], [`connect_approved`], [`connect_agree`] |
| ✅ | 🥊🥊🥊 | **A removal cuts every device of the removed user,** wherever else the device is admitted, and for good: no later admission undoes it, and only the device's own consent ties it to a user, so nobody else can cut it. Only an admin can remove another user, and nothing undoes it. | [`removal_cuts_off`], [`cut_stays`], [`cut_consented`], [`removals_iff`], [`removal_authorized`], [`removed_stays`] |
| ✅ | 🥊🥊🥊 | **A removed member's node stops holding the community, and can rejoin only as a new device.** Proven: a cut device's entry is not held, a join writes a fresh device from the node's key and never asks for an admitted one, and the removed user stays removed and its devices cut, whatever follows. A pending join is sent until a connection answers it, beside an open session or not, and a dropped session is dialed again. Tested on two SQLite nodes and over TCP, with a negative control. | [`mine_not_removed`], [`rejoin_fresh`], [`join_new_device`], [`removed_stays_removed`], [`rejoin_dials`], [`reconnect_dials`] |
| 🟡 | 🥊🥊🥊 | **A removal ends a live session's sync.** Proven: a connection carries a room synced only if the trust rule takes its peer, so a refused peer gets nothing of the room by sync and nothing of it is taken from them; what it carries of the room is only its removal's notice, and a session that carries nothing is closed. In the running node, the removal itself is enough: a node let into a community carries no sync room of it on a connection to a peer whose devices' users were removed (`sum_project`). Not yet: that every connection step reads its rooms afresh, which is in the code and tested over TCP, with a negative control. | [`rooms_cut_node`], [`rooms_trusted`], [`rooms_cut`], [`rooms_removed`], [`rooms_complete`], [`notice_then_cut`], [`trusts_live`], [`rooms_model`], [`recv_send`], [`recv_take`], [`removal_cuts_off`] |
| 🟡 | 🥊🥊🥊 | **No packet goes to a removed member but the notice of its removal.** From the first engine turn after a node decides a removal, it sends the removed user's node only that removal and its requirement closure, once, and then closes the session. Proven, per connection step: the step after a store, and each tick that does not drop the session, gives the notice when its closure fits the walk's budget; every step sends the removed node only sync wire ops, ops of rooms it still syncs, and that closure, and takes nothing of the community; a notice is given once, a have for the community gets no reply, and once every notice owed is given the session carries nothing and is closed. A handshake gets no reply, and a replayed request gets nothing. Not proven: the entry point as a whole (that the node runs those steps, writes `given` and seals before it purges), which is tested over TCP, with negative controls. | [`notice_sent`], [`closure`], [`notice_send`], [`removed_gets_only_notice`], [`notice_once`], [`notice_no_holds`], [`notice_then_cut`], [`answer_trusted`], [`resend_trusted`] |
| 🟡 | 🥊🥊🥊 | **No session before approval,** however hellos are lost or replayed, and sessions form only with trusted peers. Proven over the running code, step by step: a responder writes a connection, or re-sends one, only for a request whose initiator the trust rule takes. Not yet: the whole guarantee, through lost and replayed hellos, over the running handshake; it is proven over a model. | [`no_connection_before_approval`], [`sessions_trusted`] *(model)*, [`answer_trusted`], [`resend_trusted`] |
| 🟡 | 🥊🥊🥊 | **Peers cannot push ops in** outside the rooms they are let into, nor plant a device's local state. Proven: on a session, only ops of its rooms are taken; on the bare wire, a hello yields only a join request of its community, trusted or not, so a removed member, or an outsider who knows the community, pushes nothing else in (tested over TCP, with a negative control). Not yet: that a device's local state stays its own through purges, which is proven over the modelled purge (`purgeS`) only. | [`recv_take`], [`bare_takes_only_join`], [`intake_local`], [`stored_local`], [`local_fact_mine`], [`intakeConn_conn`] |
| ✅ | 🥊🥊 | **Both ends hold one session.** Two ends that complete a handshake hold the same hash, each names the other, and each one's send key is the other's receive key. A frame opens to what was sealed, for the connection it names. | [`established_agrees`], [`open_seal`], [`cid_seal`] |
| | | **Hostile input** | |
| ✅ | 🥊🥊🥊 | **One parse per op.** A decoded op re-encodes to exactly the bytes received, its id is their SHA-256, and a Valid op is exactly its body's encoding under its own type: no parser differential, no malleability, no renamed or re-typed op. | [`Codec.encode_decode`], [`Op.id_decode`], [`distinct_of_collisionFree`], [`op_of_valid`] |
| ✅ | 🥊🥊🥊 | **Hostile bytes decode to a well-formed value or to nothing.** A QOI picture comes out at 1–2048 px a side, with exactly its pixels' bytes, so at most 16 MiB whatever it claims; the app decodes with this decoder. An mDNS packet keeps its RFC limits, and its pointer chains end by construction. Invite links and QR segments are valid. | [`Pic.decode_sized`], [`Image.decode_sized`], [`Mdns.decode_valid`], [`Community.parse_valid`], [`Qr.parse_valid`] |
| ✅ | 🥊🥊🥊 | **Attachments authenticate themselves.** Any peer may relay a file's chunks, but a chunk is Valid only if it is its file's own slice. One op stands for each index, progress counts exactly the chunks held, and the chunks put together are the file. Assumes SHA-256 has no second preimage on the tree's inputs. | [`chunk_is_slice`], [`verify_sound`], [`complete_assembles`], [`chunk_unique`], [`progress_exact`], [`assumptions_hold`], [`no_injective_hash`] |
| 🟡 | 🥊🥊🥊 | **Judging cannot be hung.** From any state, judging empties its queue within a budget read off the tables. Not yet of the running node: proven of states whose purges are `purgeS`, a model of the SQL purge. | [`drain_bounded`], [`drain_terminates`], [`step_budget`] |
| ✅ | 🥊🥊🥊 | **Authenticate before parsing:** a sealed frame's payload is decoded only after its AEAD check passes, under the receive key of the session the frame names. A frame that fails leaves the node and its store as they were, and sends nothing. | [`sealed_auth`], [`openFrame_auth`], [`onFrame_sealed`], [`sealed_unopened`] |
| 🟡 | 🥊🥊 | **Bounded buffering:** inbound frames wait in a bounded queue, each at most 1 MiB, with one partial frame per socket, whatever the peer's length fields say; a full queue blocks its producer, and sockets are capped globally and per address. Proven of a model of the reader's loop (`keeps`); wiring it to the running reader is a todo. Tested: the queue's backpressure and socket admission. | [`buffer_bounded`], [`frames_kept`], [`frames_tooBig`], [`admit_bounded`] |
| ✅ | 🥊🥊 | **No amplification:** a decoded op is exactly its bytes, so no larger. A bundle's payloads are together smaller than it. Linear decoding time is not proven. | [`Op.decode_exact`], [`Op.decode_parts`], [`decode_sum`] |
| 🟡 | 🥊🥊 | **Resources are capped:** sockets, connection hint/ask sets, closure and replies; full rounds keep no sender closure state. Not covered: room/notice metadata, index and snapshot contents, transient allocations, and round/CPU work. | [`hold_bounded`], [`conn_bounded`], [`conn_state_bounded`], [`full_round_stateless`], [`closure_capped`], [`closure_complete_under_cap`], [`honest_no_drop`], [`work_retry_bounded`], [`onWant_authorized`], [`serveOwed_blind`], [`serveOwed_budget`] |
| ✅ | 🥊🥊 | **Live sessions stay up.** With positive `live/3` and ticks and delivery within that interval, either side sends traffic or an empty-have keepalive; only silence drops it. Unserved asks expire separately. | [`drop_iff_silent`], [`keepalive_sent`], [`live_stays`], [`asks_expire`] |
| ✅ | 🥊🥊 | **Rooms progress independently.** An idle room starts beside a stalled one; an unshown room gets an empty end without changing the connection. | [`room_independent`], [`unshown_room_answered`], [`uncarried_room_answered`] |
| ✅ | 🥊🥊 | **Purges notify readers.** Session and courier purge roots reach the app alongside stored ids. The reader's fallback poll is still present. | [`purges_notified`], [`flush_notifies`], [`close_purges`] |

### Quality proofs

| | | Guarantee | Theorems |
|---|---|---|---|
| | | **The engine** | |
| 🟡 | 🥊🥊🥊 | **Honest nodes agree.** The same ops, in any order, batching or interleaving, give the same verdicts. Not yet of the running node: proven of states whose purges are `purgeS`, a model of the SQL purge. | [`same_ops_same_verdicts`], [`order_free`] |
| ✅ | 🥊🥊 | **Verdicts are the spec's, and final.** Once judging settles, every stored verdict is the spec's over the ops received, and no later op changes it. | [`drain_settles`], [`status_iff_spec`], [`spec_extends`], [`inv_ingest`], [`inv_step`] |
| ✅ | 🥊🥊🥊 | **Taking an op in twice is taking it in once.** Proven of the running intake (each write turn's `ingest`, through `run_ingest` and `run_ingestEach`): an op the store holds changes nothing, the same op twice leaves the store as once, and after a write turn's ops any of them again changes nothing. So a retried write, a peer's resend, or an op written here and synced back is harmless: nothing is stored or queued twice, and every verdict stays. | [`ingestS_known`], [`ingestS_twice`], [`ingest_twice`], [`run_ingestEach`], [`ingestAll_again`] |
| 🟡 | 🥊🥊🥊 | **Purge is safe.** A purged session or courier is gone, no shared op is ever deleted, and the engine settles on what remains. Not yet: proven of the purge's model (`purgeS`); the running purge is SQL, tested against it. | [`purge_gone`], [`purge_shared`], [`purge_settles`] |
| 🟡 | 🥊🥊 | **Purge takes exactly what it must.** It takes the named conn and local ops and their stored dependents. Shared dependents are judged again. Not yet: proven of the purge's model (`purgeS`); the running purge is SQL, tested against it. | [`purge_named`], [`purge_undecides`], [`purge_inv`], [`mem_purgeSet`], [`reach_ops`] |
| ✅ | 🥊 | **Families compose, op by op:** adding a family changes no verdict or scope of the first's ops. Strict decoding round-trips. | [`sum_left`], [`sum_scope_left`], [`Codec.decode_encode`], [`Op.decode_bytes`] |
| ✅ | 🥊🥊🥊 | **The Community laws hold in the running node** (`sum_project`). The node's store holds Community and Connection ops. Its Community part is the Community ops, with Community's own verdicts. At rest, that part keeps Community's invariant, and its ops are Valid exactly where the node's are. A view that reads only Community relations answers in the node as in that part, as the trust rule, members and recipients do. So the laws above hold of the node that runs. Tested too: over TCP, the node's trust rule, members and recipients match a Community-only store of its Community ops, before and after a removal. | [`sum_project`], [`sum_project_node`], [`spec_sum_left`], [`view_proj`], [`connect_iff_node`], [`members_iff_node`], [`recipients_iff_node`], [`node_settles`] |
| ✅ | 🥊🥊🥊 | **The honest path works.** A request with its invitation and both signatures is valid, an eligible member's approval is valid, and enough approvals admit and let the device in. The remover's intent writes only removals that stand. | [`request_valid`], [`approve_valid`], [`admit_admits`], [`connect_admitted`], [`removeMember_valid`] |
| | | **Sync** | |
| 🟡 | 🥊🥊🥊 | **A sync round is complete.** Each side is sent exactly what the other holds in the range and it lacks. On any path, it takes at most one answer more than the two sides hold in the range. Not yet: proven of the round's model (`exchange`); wanted of the running round (`conn_runs_exchange`). | [`exchange_complete`] |
| ✅ | 🥊🥊 | **Fingerprints are honest.** Equal Merkle labels mean equal sets, and a side opens a round with an honest claim. | [`lbl_inj`], [`opening_honest`], [`num_inj`] |
| 🟡 | 🥊🥊🥊 | **Partial sync is safe.** A node that holds an op's requirement closure judges it as its peer does. Not yet: proven of the spec, which running judging reaches only on states whose purges are modelled. | [`spec_local`] |
| 🟡 | 🥊🥊🥊 | **A joiner connects, and both sides converge,** over a socket that loses, duplicates and reorders. Proven over a model only. Wanted: the same of the running code (`conn_runs_exchange`, `closure_delivered`). | [`bootstrap`], [`bootstrap_ideal`], [`bootstrap_possible`], [`reachable_inv`] *(model)* |
| 🟡 | 🥊🥊🥊 | **The running connection does all this.** Proven: a connection answers a claim that lists ids exactly as `exchange` does, from the round's snapshot. Not yet: the whole round under any delivery order (`conn_runs_exchange`), and each op's requirement closure (`closure_delivered`). | [`conn_answers_ids`] |
| 🟡 | 🥊🥊🥊 | **New ops reach connected members.** In a world of two nodes running the sync code on held stores, with fixed rooms, frames in the clear and no handshake: an op written while a member's session is up is offered at once, and the member holds it after one exchange (the offer, a want, the op), when both sides' rooms include its room, neither held it, and the receiver has a free ask slot and a response budget. Not yet of the runner, with TCP, sealed frames, the trust rule's rooms and the handshake. | [`stream_offered`], [`stream_delivers`], [`stream_delivers_steps`], [`stream_offered_runs`], [`stream_delivers_runs`] |
| ✅ | 🥊🥊🥊 | **Every want is served in full, and in order.** A want's authorized ids join the session's queue behind what it already owes, each id once, and each step serves the queue from its front within the room its socket has, so the id at position p is served within p + 1 steps (in the same step, on an empty queue). Nothing is truncated or retried; an ask whose op the peer has since purged expires. | [`onWant_all`], [`onWant_order`], [`serveOwed_head`], [`serveOwed_fifo`], [`owed_within`], [`want_sends`], [`asks_expire`] |
| 🟡 | 🥊🥊🥊 | **A new op never waits behind backlog.** The app's write is the runner's next event, whatever frames are queued. On each socket, messages naming few ids and the wanted ops this node just wrote go out in the next native write, ahead of every queued want answer, so only the write under way and urgent frames reach the socket first, and a socket's queue stays under its cap. Not yet: `fresh_stmt` over the World (a write reaches a neighbour within a bound independent of backlog) is not proven; these laws discharge its send-path premise, and the receiver's inbound queue is still FIFO, a bounded constant (`queue` frames). That one socket's backlog holds up no other is tested over TCP, not proven. | [`write_first`], [`write_within`], [`urgent_ahead`], [`ahead_bytes`], [`cut_bytes`], [`push_capped`], [`serveOwed_hot`], [`hot_ids`], [`lane_control`], [`fresh_served`], [`write_hot`] |
| ⬜ | 🥊🥊🥊 | **Everyone converges.** Wanted: under fair delivery, members linked by any chain of connections eventually hold every op of their community, and so the same verdicts. Proven so far for two nodes, over a model. | |
| ⬜ | 🥊🥊 | **Staleness is never hidden.** Wanted: "up to date as of T" means a round this device opened at T ended with it holding everything the peer held in that room, and a sync that stalls is shown within a stated bound. | |
| ⬜ | 🥊🥊🥊 | **A synced page is complete:** after syncing a page, a device shows every row its peer shows for it (`page_sync`). | |
| ⬜ | 🥊🥊 | **Sync is efficient.** Each op is sent at most once per connection, and a round needs at most fan·Δ·⌈log n⌉ claims. | |
| ⬜ | 🥊 | **The cached Merkle tree's labels are `lbl`'s,** for O(log n) fingerprints with no change on the wire. | |
| | | **The screen** | |
| ✅ | 🥊🥊 | **Unmounted pages issue no new reads or writes.** The running read/write gates reject unmounted pages and old leases, including after remount. Cache pruning leaves exactly the mounted queries after each has an answer; watches are their keys. Worker retirement, bounded suspend and native callback delivery are tested, not proved by these gate laws. | [`unmount_read`], [`unmount_write`], [`old_callback`], [`unmounted_quiet`], [`old_quiet`], [`live_exact`], [`subscriptions_exact`], [`mounted_runs`] |
| 🟡 | 🥊🥊 | **Lifecycle state survives a restart or resize.** Proven: the running checkpoint codec and application preserve page and message anchor, and resize's offset keeps the anchor's top-edge distance when it fits. Not yet: SQLite crash durability as a Lean law; the headless twin tests crashes, viewport changes, keyboard transitions and invite launch ([inventory](docs/LIFECYCLE.md)). Placement is supplied by the shared Lean seam below. | [`restore_checkpoint`], [`page_round`], [`restore_page_anchor`], [`apply_page_anchor`], [`resize_anchor`], [`viewport_geometry`], [`viewport_possible`] |
| 🟡 | 🥊🥊🥊 | **Nothing on screen is covered or mis-tapped.** Content in the viewport is drawn below the header, and above the composer and keyboard. Pinned to the bottom, the newest message is wholly visible. A tap lands on the row, or emoji key, drawn under it. The phones and twins call the shared placement and input functions. Not yet: OS event acquisition and compositor pixel copies as Lean laws. | [`Surface.visible_in_viewport`], [`newest_visible`], [`Surface.pinned_visible`], [`pinned_tap`], [`hit_iff`] |
| ⬜ | 🥊🥊🥊 | **Every control is big enough to tap.** Every tappable control's hit area, not just its drawn size, is at least 48 dp by 48 dp on Android and 44 pt by 44 pt on iOS, at every supported screen size and text scale. | |
| ⬜ | 🥊🥊 | **A tap means one thing.** On every screen, no two controls' hit areas overlap, so a point selects at most one control. A tap selects the control drawn under it. Today this is proven for the emoji sheet and message rows only (`keys_disjoint`, `hit_iff`, `pinned_tap`). | |
| ⬜ | 🥊🥊 | **Every control shown can be tapped.** A control that is drawn has its hit area on screen, and not under the header, the composer or the keyboard. | |
| 🟡 | 🥊🥊🥊 | **Typing and sending never wait on sync.** A frame never waits on the node, however full its inbound channel. Proven of the running offer (`offerList`, which `submit` and each frame's re-offer run with the channel's `trySend`), whatever the channel answers: what it took, then what waits, is every write submitted, in order, over any run of sends and frames (none lost, none twice, none overtaken; and one taken twice would be harmless anyway, `ingestAll_again`). Tested: `nodequeue`, over a real full channel (the offer returns at once; the control, the blocking send, waits). Checked at build: no frame path, short of the threads it starts, reaches `Engine.Sync.enqueue` (so not `Runner.write`), a channel's waiting `send`, `IO.wait`, or a store commit (`Lifecycle.save`: a node's purge holds SQLite's write lock until the frame's read ends, so the frame hands its checkpoint to the writer's thread) (tests/Wiring.lean's `block`, whose negative controls, `submit` and the checkpoint as they were, are caught; `lifecycle_node`'s purge test runs a real purge checkpoint inside a frame). Not yet: a `Task.get` of a task not yet finished is not checked, and `trySend` returning without waiting is assumed, as the platform's other primitives are. | [`offer_split`], [`offer_runs`] |
| ⬜ | 🥊🥊 | **A tap acts once.** A second tap on a control while its action is in flight starts nothing new (Send sends once). A press that turns into a scroll past the slop is not a tap. | |
| ⬜ | 🥊🥊 | **Destructive actions are guarded.** Every action that cannot be undone asks for a second confirmation, as removal does (`writes_only_after_two`). Its control keeps a clear gap from the controls around it. | |
| ✅ | 🥊🥊🥊 | **A screen re-reads only what changed.** A list changes only when a row is filed under a key it read, and no list holds an op twice. | [`eval_stable`], [`view_stable`], [`filed_rel`], [`mem_keysOf`], [`matching_nodup`] |
| 🟡 | 🥊🥊🥊 | **Notices are exact.** A screen watches windows: a list's rows between two positions. Proven: after any batch of commits and purges, the journal's rows, netted and matched against an index of windows, notify a subscriber exactly when one of its windows changed, never for a row outside them or one filed and purged within the batch, given one op per id; a read's window, cut at its last row, changes exactly when its rows do, and holds exactly them; a read's watch misses nothing its reader uses; matching a filing costs a hash and ⌊log₂ 2S⌋+2 comparisons; the frame's wants (`Screen.Frame.wants`) are exactly its page's reads, the near rows' hull per list key and the near rows' reads. Notices by key, and an unnetted journal, are shown imprecise. The app's cache watches each read's window, takes its notices from the journal netted, and unwatches a component's reads when it unmounts (`agrees_notice`, `agrees_unmount`, `watched_held`); the conversation is a window of rows about an anchor, watched by exactly its rows, and the counts beside it are a read of the page's own. Not yet: the window holds up to 100 rows past each end of the near rows (`past_hull_le`), and the frame does not want by `Frame.wants`; a union read (the conversation) is precise per key, not for the union's own cut; reads of an op's bytes are outside. SQLite's triggers are tested against the model (`window_check`), not proven. | [`notice_iff`], [`read_notice_iff`], [`read_rows_iff`], [`Engine.window_rows`], [`watch_stable`], [`run_exact`], [`fact_stable`], [`find_costs`], [`notify_cost`], [`screen_subs`], [`hull_near`], [`past_hull_le`], [`key_notice_imprecise`], [`unnetted_imprecise`], [`keep_scrolled_off`], [`agrees_notice`], [`agrees_unmount`], [`watched_held`] |
| ✅ | 🥊🥊🥊 | **Removing someone takes two confirmations.** Nothing is written before the second, and cancelling writes nothing. Each attempt starts fresh, and one in flight cannot be replaced. The action is offered only to an admin, on another present member. | [`writes_only_after_two`], [`cancel_writes_nothing`], [`open_fresh`], [`no_replace`], [`offered_only`] |
| ✅ | 🥊🥊 | **Back goes back.** Back after opening a page restores the state before it (only the page's one-line field is cleared). Back at a root does nothing, and after a switch no number of backs leaves the new home. No page is twice in the back stack, so fewer than 19 backs reach a root. No step changes the composer's draft, and the native field follows it. | [`back_go`], [`NavLaws.back_open`], [`NavLaws.back_root`], [`back_switch`], [`go_inv`], [`NavLaws.depth`], [`draft_back`], [`into_native`] |
| ✅ | 🥊🥊 | **The people list is the present members,** each once: users with a live device. A removed member leaves it and its count, but keeps their name on their messages. | [`present_iff`], [`present_not_removed`], [`present_nodup`] |
| 🟡 | 🥊🥊🥊 | **The screen is one moment.** Every frame is drawn over a single store state, the latest the app has seen. Proven over the running cache (`Live.readWith`, which the frame's and the reader's reads run), given SQLite's snapshot isolation and the journal hypothesis (Assumed): every read through it, cached or not, returns its moment's answer; and a model of the reader's pass, making its decisions (`Live.mark`, `Live.pick`), marks every want whose reads went stale before reading any. Not yet: `Reader.pass` itself as a law (TwoNodes tests it), one moment across the reader's board and the frame's own reads (each is consistent; they settle, BoardLaws' `settle`), a frame that writes spans more than one outbox moment, the outbox's notice keys derived from its ops, and `step` itself as a statement. | [`read_one_moment`], [`answer_agrees`], [`agrees_store`], [`agrees_notice`], [`agrees_keep`], [`agrees_empty`], [`eval_stable`], [`view_stable`] |
| 🟡 | 🥊🥊🥊 | **Scrolling always shows something.** Proven of the running frame's `Cover.seen`: from the bottom padding up to the last loaded row's top, and above it while older messages are outside the window, no position is blank, and a bitmap line is shown only where its row has it. At every vsync, the compiled scalar Lean functions translate the published buffer by the offset change and fill outside it with the same `holdLine` tile. This composes with the frame's coverage law; pinned pages stay still. The reader reads a window of at most 200 about an anchor and counts the rest. Not yet: bounded frame work or an OS scheduling guarantee. | [`Cover.covered`], [`Cover.line_painted`], [`Translate.covered`], [`Translate.equivariance`], [`Translate.fill_pixel`], [`Slide.edge_eq`] |
| ⬜ | 🥊🥊 | **An action's toast stays until the screen shows it.** A toast for an action (removing someone, a new name or avatar) stays up until every component on screen has re-read a state that holds the action's op, or until the OS's toast time passes, whichever comes first. So a toast that leaves early proves the screen has caught up. | |
| 🟡 | 🥊🥊 | **The layout is exact.** Proven of the running code: the sheet's composition and its emoji keys (the painter places item i by `itemAt` and the sheet's lines by `lineOf`, exactly over the box the taps answer for: `lineOf_ctop`), the composer's photo chips (in order, never overlapping, an X that never reaches the next chip, and all four on screen), the invite's hints and QR, and the camera preview. The slide, keyboard shift and pinned-page placement now run through `Surface` and scalar `Slide` exports. Not yet: graphics API application and pixel copies as Lean laws. | [`Surface.placed_row`], [`Surface.newest_drawn`], [`Surface.pinned_row`], [`keys_disjoint`], [`hit_cell`], [`reachable`], [`itemAt_place`], [`lineOf_ctop`], [`chips_apart`], [`x_clear`], [`chips_fit`], [`compose_row`], [`compose_top`], [`Link.hints_fit`], [`Link.qr_fits`], [`Camera.src_in`] |
| 🟡 | 🥊🥊🥊 | **Message text is shown faithfully.** Proven: wrapping drops only spaces, keeps every other character in order, and every line fits when every character does; bidi reordering drops and invents nothing; the glyphs placed are exactly the visible characters; and every resolved European or Arabic number run, with its separators and terminators (decimals, times, percentages), stays contiguous and in logical order in either paragraph direction (#3). Tested: Unicode 16's BidiTest and BidiCharacterTest, 73,599 cases and 0 failures, in the scope the renderer implements (P2–P3, W1–W7, N1–N2, I1–I2, L1–L2, single lines without explicit embeddings, isolates or paired brackets; docs/BIDI.md names the 788,349 cases left out). Not yet: the bidi algorithm itself as a law (its rules are tested; the number runs are proven), embeddings and isolates, paired brackets (N0), mirrored glyphs (L4), marks (L3), paragraphs across soft wraps, and `layout` as one statement. | [`wrap_keeps`], [`wrap_fits`], [`visual_perm`], [`place_shows`], [`place_starts`], [`numbers_keep_order`], [`arabic_numbers_keep_order`] |
| 🟡 | 🥊🥊🥊 | **Names are shown correctly.** Proven: a row's name is its author's newest valid profile's, which only a device admitted into that user can write, cut to a logical prefix; explicit bidi controls (embeddings, overrides, isolates, LRM, RLM and ALM) have no directional authority: the running bidi classes each as a neutral, though one inserted can still split a number run; a name starts next to the avatar whatever its direction (as do a message's lines, start-aligned as libquiet's); and a row is marked "⚠ Duplicate" exactly when another member's name looks alike (equal once invisible characters are dropped and spaces, and the glyphs the font draws empty, collapsed). Not covered: look-alike letters across scripts, and invisible characters in a message's body. | [`message_read`], [`profile_read`], [`profile_authorized`], [`no_renaming`], [`name_placed`], [`oneLine_prefix`], [`controls_neutral`], [`marks_invisible`], [`namesake_iff`], [`row_marked`], [`twin_shown`], [`twin_before_time`], [`hit_twin`], [`name_starts`], [`flush_shows`] |
| 🟡 | 🥊🥊 | **Noto coverage and its cache are bounded.** Proven: Lean's reader uses checked indices, returned coverage fits its bitmap and declared overhang, coverage saturates, and cache insertion stays within a 4 MiB charge and 1,024 entries. Source.bitmap's compiled equivalence is tested, not proven. Not yet proven: pixel fidelity or native allocator/RSS bounds; the compact index and raster are checked against fontTools ([report](docs/NOTO.md)). | [`Ttf.byte_in_bounds`], [`Ttf.cmap_entry`], [`Ttf.coverage_value`], [`Ttf.raster_valid`], [`Ttf.raster_pixel`], [`Ttf.Cache.put_bound`], [`Ttf.Cache.put_payload_bound`] |
| ✅ | 🥊🥊 | **Times, reactions and pictures are shown as held:** the claimed time's clock, each reaction's count of distinct reactors, and each picture at its aspect inside its box. One pill per emoji, whose reactors are exactly who reacted with it, each once; a picture's box has one side at its bound and the other scaled by its aspect. | [`time_shown`], [`message_read`], [`tally_nodup`], [`tally_mem`], [`picBox_aspect`] |
| 🟡 | 🥊🥊🥊 | **What you see is what was sent.** Proven over a model where every list read is the engine's: a shown message is a valid fact of the store, its row's name, time and text are its author's name, its claimed time and its body opened with a key the store holds, and the conversation is exactly the messages under keys this device holds. Not yet: from the row's layout to its pixels. | [`message_read`], [`readable_held`], [`readable_complete`], [`eval_stable`] |
| ✅ | 🥊🥊🥊 | **Every community is reachable, and is one entry.** A switcher row's tap selects exactly the entry it draws, every entry has a row, no two entries share an acceptance or a community, and a page is drawn from its key alone, which names its entry's op, never a name. | [`switcherOrder_sound`], [`switcherOrder_complete`], [`dedupe_nodup`], [`dedupe_one_per_community`], [`select_tapped_dedupe`], [`drawPage_key`], [`pageIn_acc`] |
| ⬜ | 🥊🥊 | **The screen keeps up.** Wanted: input first, no blank rows past a latency bound, within a frame budget, with bounded reads. | |
| ✅ | 🥊🥊 | **Display order.** A channel sorts by a counter its devices share, then the time, then the id, with no ties, so devices with the same ops order it alike. Past the counter's cap, each device's own arrival order shows instead, and that exception is itself a law. | [`msg_cmp`], [`time_is_display`], [`order_total`], [`Pos.cmp_eq_iff`], [`Pos.cmp_lt_trans`], [`send_after`], [`arrival_order`], [`receipt_once`], [`order_local`], [`display_agrees`], [`readable_held`], [`readable_complete`] |
| | | **Codes, pictures and discovery** | |
| ✅ | 🥊🥊 | **What the encoders write reads back.** This holds for QR segments and codewords, invite links and mDNS packets. QR error correction is sound, and format and version readings tolerate their designed bit errors. | [`parse_segsBits`], [`parse_dataStream`], [`RS.correct_sound`], [`RS.correct_clean`], [`decodeFormat_correct`], [`decodeVersion_correct`], [`parse_text`], [`Base62.decode_encode`], [`Mdns.decode_encode`], [`decode_roundtrip`] |
| 🟡 | 🥊 | **Pictures render whole:** scaled and composited pictures are well-formed and opaque, and the tray's layout fits. Not yet: proven of `Pic`, which only qr's Android harness runs; the app draws its own. | [`render_wellFormed`], [`render_opaque`], [`scale_wellFormed`], [`fit_round`], [`Pic.layout_inside`], [`Pic.layout_apart`] |

The theorems not listed here are lemmas. The axiom audit,
`tests/Axioms.lean`, lists them all.

### Not yet about running code (todo)

A law is about running code when every definition its statement names
runs from the app's `main` or the node's runner, or is proven equal to
code that does. `tests/Wiring.lean` classifies every law from the code,
with `tests/wiring.txt` for what the code cannot say, and
`ci/proof-links.py` writes these tables and the lead's count.

<!-- wiring:begin -->
**751 of 973 laws are about running code;** another 10 run its node code in a World, and 212 are not yet. Stated only: none. 20 laws are negative controls: each proves a mutant breaks its law (they are not counted here, nor in the lead).

| Area | Laws | About running code | In a World | Not yet |
|---|---|---|---|---|
| Engine | 174 | 103 |  | 71 |
| Sync | 151 | 142 |  | 9 |
| mDNS | 3 | 0 |  | 3 |
| Node and wire | 61 | 40 | 10 | 11 |
| Bootstrap | 11 | 0 |  | 11 |
| Connections | 68 | 60 |  | 8 |
| Community | 175 | 163 |  | 12 |
| QR codes | 10 | 10 |  |  |
| Pictures | 13 | 1 |  | 12 |
| Screen | 235 | 177 |  | 58 |
| App | 72 | 55 |  | 17 |

| Missing link | Laws | To make them real |
|---|---|---|
| `World.peer`, `Setup.sync`, `Who.other` +7 | 10 World laws; not yet: [`write_offers`], [`hold_wants`], [`want_sends`]†, [`op_taken`], [`write_offers_all`], [`write_hot`]†, [`secrecy_runs`] | Real: both nodes are the running `Engine.Sync.Node`, its entry points run on held stores. Assumed: the network may deliver, duplicate, drop or delay any frame, and sessions open directly, with plain frames (no handshake). Wanted: the World with the app's own `Sync` (the Connection family, sealed sessions, the handshake), which makes these laws wired. |
| `Engine.purgeS`, `Engine.purgeSet` | [`order_free`]*†, [`reach_drain`], [`drain_terminates`]*†, [`drain_settles`]*†, [`same_ops_same_verdicts`]*†, [`stored_local`]*†, [`local_fact_mine`]*†, [`drain_bounded`]*†, [`step_budget`]*†, [`purge_gone`]†, [`purge_named`]†, [`purge_shared`]† +21 more | The running purge is SQL (`purgeSql`), only tested against this model: write purge once over the store, as `drain` is, and bridge it (`run_purge`). |
| `Sync.exchange` | [`exchange_complete`]†, [`conn_answers_ids`]°†, [`exchange_ids_stable`], [`exchange_log`], [`exchange_stable`] | The round's model: prove the running round (`Conn.onRbsr`) performs it under any delivery order (`conn_runs_exchange`). |
| `Community.recipients`, `Community.members` | [`recipients_iff`]†, [`members_iff`]†, [`reads_members`], [`reads_recipients`], [`members_iff_node`]†, [`recipients_iff_node`]† | The key-wrap writers (`found`, `approve`) do not read `recipients`: wrap through the query, and tie a wrap's recipient to an admission. |
| `Scene.approval`, `Scene.K`, `Scene.S` +12 | [`no_connection_before_approval`]†, [`sessions_trusted`]†, [`bootstrap_possible`]†, [`bootstrap`]†, [`bootstrap_ideal`]†, [`reachable_inv`]†, [`admitted_inv`], [`allowedA`], [`allowedB`], [`allowPeer_iff`], [`allowPeer_settles`] | The bootstrap's model (ops/connection/bootstrap/): retired by `conn_runs_exchange`, `closure_delivered`, `answer_trusted` and `untrusted_silent` over the running code. |
| `Sync.keeps` | [`buffer_bounded`]*† | The model of the TCP reader's loop (engine/wire/Tcp.lean): have the loop step by it, or prove its buffers are `keeps`'s. |
| `Pic.add`, `Geom.box`, `Pic.attachEdge` +4 | [`fit_small`], [`fit_le`], [`fit_pos`], [`fit_long`], [`fit_round`]†, [`layout_sizes`], [`Pic.layout_inside`]†, [`layout_apart`]†, [`add_stored`], [`scale_wellFormed`]†, [`render_wellFormed`]†, [`render_opaque`]† | The composer's tray runs only in qr's Android harness; the app attaches with its own: use `Pic`'s tray in the app, or prove these of its code. |
| `Mdns.decode`, `Mdns.encode` | [`Mdns.decode_encode`]†, [`decode_valid`]*†, [`decode_roundtrip`]† | Nothing that runs discovers peers by mDNS (tests/mdns runs `Mdns.Net`): have the runner announce and browse with it. |
| `Arrival.lit` | [`lit_zero`], [`lit_mono`], [`lit_full`], [`lit_clockwise`], [`ring_counts`] | `paintRing` tests `onRing` and `arc` inline: have it paint by `lit`. |
| `Frame.wants`, `Subs.ofList`, `Frame.listWins` +2 | [`has_ofList`], [`ofList_wf`], [`screen_subs`]†, [`hull_near`]†, [`past_hull_le`]†, [`screen_index`], [`keep_scrolled_off`]† | Nothing that runs wants by `Frame.wants`: the frame wants the conversation's window and the near rows (App.lean); want by it, the window cut to the near rows' hull (Screen's plan). |
| `Pics.after`, `Pics.costIn` | [`decoded_started`], [`image_steady`], [`image_settles`], [`image_twice`] | The picture doors as data (`PicM`), measured: the app's own doors (its decode table and frame counter) are not shown to answer as `PicM`'s. Prove they do, or state these over them. |
| `Board.apply`, `RWorld.commit`, `RWorld.evict` +10 | [`RWorld.acts_shown`], [`seen_take`], [`World.inv_commit`], [`RWorld.inv_commit`], [`RWorld.inv_pass`], [`RWorld.inv_frame`], [`inv_evict`], [`RWorld.settle`], [`World.inv_pass`], [`World.inv_frame`], [`World.settle`], [`marked_pass`] +7 more | The change signal's reader and frame, as Worlds (engine/renderer/BoardLaws.lean, ReaderLaws.lean): the app's reader runs `Board.put`, `take` and `keep`, and decides by `Live.staleW`, `mark` and `pick`, but the laws of a pass and a frame are over the Worlds. Todo: state them of `Reader.pass` and the frame's `takeBoard`. |
| `T.sum`, `Both.bottom`, `Both.rowAt` +16 | [`start_eq`], [`find_spec`], [`set_toList`], [`push_ok`], [`findM_cost`], [`startM_cost`], [`setM_cost`], [`rows_cost`], [`start_mono`], [`start_size`], [`below_window`], [`above_window`] +8 more | The row-heights tree (engine/renderer/Heights.lean): the app keeps its rows' heights in a map (`App.heightOf`) and adds them up itself. Have its list frame place rows by `Heights`. |
| `PageId.all` | [`NavLaws.depth`]† | Nothing that runs calls it. |
| `Plan.stmts` | [`plan_stmt_cost`] | Nothing that runs calls it; `Engine.readPlan` do. |
| `SeekCost.seek` | [`plan_stmt_cost`], [`readPlan_cost`], [`readPlan_cost_le`], [`readPlan_cost_range`] | Nothing that runs calls it; `Stmt.cost` do. |
| `Stmt.cost` | [`plan_stmt_cost`] | Nothing that runs calls it; `Engine.planCost` do. |
| `Stmt.walks` | [`walks_le`] | Nothing that runs calls it; `Stmt.cost` do. |
| `Sync.get` | [`fold_congr`] | Nothing that runs calls it. |
| `Sync.give` | [`fold_congr`] | Nothing that runs calls it. |
| `Sync.retried` | [`work_retry_bounded`]† | Nothing that runs calls it. |
| `View.listsAt` | [`deviceLive_lists`], [`live_lists_ge`], [`live_lists_le`], [`presentW_lists`], [`presentW_lists_eq`], [`present_lists_eq`], [`present_scans`], [`unremoved_lists`] | Nothing that runs calls it. |
| `Engine.inlRow` | [`matching_proj`], [`eval_proj`], [`filterMap_inlRow`] | Nothing that runs calls it. |
| `Engine.insertBy` | [`insertBy_map`], [`foldr_insertBy`], [`insertBy_merge`] | Nothing that runs calls it; `Engine.sortPos` do. |
| `Engine.leftValid` | [`mem_proj_idx`] | Nothing that runs calls it; `Engine.DB.proj` do. |
| `Engine.planCost` | [`readPlan_cost`], [`readPlan_cost_le`], [`readPlan_cost_range`] | Nothing that runs calls it. |
| `Engine.readPlan` | [`readPlan_cost`], [`readPlan_cost_le`], [`readPlan_cost_range`] | Nothing that runs calls it. |
| `Engine.sideCount` | [`sideCount_run`], [`splitWalk_cost`], [`splitWalk_exact`], [`splitWalk_steps`] | Nothing that runs calls it. |
| `Engine.sortPos` | [`perm_sortPos`], [`sortPos_eq_fast`], [`sortPos_sorted`], [`sortPos_map`], [`mergeRuns_eq_sortPos`], [`union_rows`] | Nothing that runs calls it; `Engine.matching` do. |
| `Engine.sortPosFast` | [`sortPos_eq_fast`] | Nothing that runs calls it; `Engine.sortPos` do. |
| `Engine.specVerdict` | [`specVerdict_eq_some`] | Nothing that runs calls it; `Engine.DB.proj` do. |
| `AWorld.pass` | [`AWorld.passActs_comp`], [`AWorld.passActs_indep`], [`AWorld.passActs_acts`] | Nothing that runs calls it. |
| `AWorld.type` | [`AWorld.type_only`] | Nothing that runs calls it. |
| `RWorld.actsWorld` | [`passActs_picks`] | Nothing that runs calls it; `RWorld.passActs` do. |
| `RWorld.commitAll` | [`passActs_picks`] | Nothing that runs calls it; `RWorld.actsWorld`, `RWorld.nTouched`, `RWorld.passLate` do. |
| `RWorld.markIdx` | [`passActs_picks`] | Nothing that runs calls it; `RWorld.passIdx` do. |
| `RWorld.nTouched` | [`passActs_picks`] | Nothing that runs calls it; `RWorld.passActs` do. |
| `RWorld.passActs` | [`passActs_nil`], [`inv_passActs`], [`idxok_passActs`], [`RWorld.acts_shown`] | Nothing that runs calls it; `AWorld.pass` do. |
| `RWorld.passIdx` | [`passActs_nil`] | Nothing that runs calls it; `RWorld.passActs`, `RWorld.passLate` do. |
| `RWorld.touched` | [`passActs_picks`] | Nothing that runs calls it; `RWorld.actsWorld`, `RWorld.nTouched` do. |
| `PeopleLaws.admIn` | [`live_lists_ge`], [`present_scans`] | Nothing that runs calls it. |
| `Want.withViewLast` | [`withViewLast_moves`] | Nothing that runs calls it. |
| `Screen.far` | [`keep_scrolled_off`]† | Nothing that runs calls it; `Screen.frame2` do. |
| `Screen.frame2` | [`keep_scrolled_off`]† | Nothing that runs calls it. |
| `Screen.keepAll` | [`keep_scrolled_off`]† | Nothing that runs calls it. |
| `Bidi.numberRuns` | [`run_contiguous`]* | Nothing that runs calls it; `Text.numberRuns` do. |
| (none) | [`spec_extends`]†, [`distinct_of_collisionFree`]†, [`spec_local`]†, [`erase_run`], [`erase_pure`], [`erase_bind`], [`erase_charged`], [`erase_chargedBy`], [`erase_lift`], [`erase_tick`], [`val_erase`], [`cost_run`] +32 more | Nothing to wire: each is about a specification or an assumption. |

\* only a premise names it. ° about running code, but names it beside. † a guarantee above cites it.

| Assumption | Laws | |
|---|---|---|
| [`Unforgeable`] | 2 | An Ed25519 signature that verifies under a device key was made by that key's holder. |
| [`CollisionFree`] | 22 | SHA-256 has no collision among the ops a node received. |
| [`offerM`] | 2 | The node's channel, answering each offer yes or no in any sequence: `offerList` is generic over it, run with `trySend`. |
| [`NoSecondPreimage`] | 14 | SHA-256 has no second preimage on a file's Merkle tree inputs. |
| [`Suite.Good`] | 6 | X25519 agrees, the AEAD opens what it seals, and public keys are 32 bytes (correctness only). |
| [`Seal.Good`] | 4 | The seal's AEAD and key wrap open what they seal (correctness only). |
| [`Symbolic.sym`] | 13 | The symbolic model of the cryptography, over which the running handshake runs. |
| [`Model.run`] | 293 | The store model: SQLite's reads, writes and write turns answer as the model's tables (tested by tests/engine/Differential.lean and QueryDiff.lean). Not its purge: `purgeS` is a model. |
| [`Sync.popW`] | 3 | The run loop's two channels, as queues: `tryRecv` on a `Std.CloseableChannel` takes its oldest value (Lean's library). |
| [`Engine.runJ`] | 4 | The store's journal (triggers on the index, `Db.filings`) records what this model's journal records, batch by batch (tested by tests/engine/WindowCheck.lean). |
| [`Engine.Inv`] | 86 | The tables' invariant. Purges keep it only by `purge_inv`, over the model `purgeS`, and the purge test (tests/engine/Purge.lean). |
<!-- wiring:end -->

## What isn't Lean, and why

**Lean decides; native code carries.** Lean runs the engine, the
protocol and the UI, and paints every pixel the app shows. But only the
OS can open a window, deliver a touch or show a keyboard, and its APIs
are C, Java and Objective-C. So each platform wraps Lean in a thin
native shell, and the engine sits on two vetted libraries. Where they
meet Lean is the *seam*, and there are six places it runs:

- **Input in.** Touches, the keyboard's text, the screen's insets, the
  camera's frames and the clock, through Platform.lean's 19 externs;
  touches come as small fixed-size events, in the order the OS gave
  them.
- **Pixels out.** Lean hands over finished rows of pixels for three
  layers (list, header, composer), plus a hold tile and placement; native code
  copies them into the OS's buffers.
- **Scrolling.** The OS's own physics moves the offset, and Lean draws
  at it.
- **Storage.** Three calls into SQLite: open, exec, and one statement.
- **Crypto.** SHA-256, Ed25519, X25519 and two AEADs, from vetted Rust
  crates behind one C file.
- **Tests.** A control channel, in development builds only, through
  which tests drive the app as a person would.

The network is not one of them. The handshake, framing, sync rounds,
the trust rule and judging are Lean, and so are the TCP and UDP sockets
under them (Std.Async, over Lean's runtime).

**Most of the platform code is there so scrolling feels native.** A chat
app is judged by its scroll, and two things make one feel right:
- **Speed.** Lean's frames go to the OS's compositor as layers, and a
  native vsync thread slides the list layer to the current offset on
  every refresh, whether or not Lean has a new frame yet. The list moves
  at the display's rate while Lean is busy with sync, and Lean draws
  each frame at the offset predicted for when it shows.
- **Familiarity.** Fling speed, deceleration, the bounce at the ends,
  how a drag hands off to a fling: people know these by feel, and they
  differ between Android and iOS. Rather than reverse-engineer Google's
  and Apple's curves in Lean, the app uses the real ones: Android's
  VelocityTracker and OverScroller with the device's ViewConfiguration,
  and on iOS an actual UIScrollView, turned upside down so its offset is
  the chat's bottom-anchored one. A fling feels like every other list on
  the phone because it is one. (Moving the physics into Lean is possible,
  and listed [below](#what-else-can-we-move-into-lean).)

The keyboard is the same story: a hidden EditText on Android and a
UITextField on iOS hold the composer's text, so every input method,
autocorrect, dictation and composition works as people expect, and Lean
draws the result.

**Why this is not a big deal for safety.** The app's safety properties
(who can post, join, read and remove; what sync discloses; whom the
trust rule lets in; that no op can be forged or altered) are decided in
Lean, over the bytes that come off the network. The shells never parse
an op, hold a key or name a member. So when native code is wrong, it
fails in ways orthogonal to those properties: a list drawn a few rows
off, a dropped touch, a fling that stutters, a crash. Those failures are
visible and immediate, the kind testing on devices finds, and none of
them forges a message, leaks a key or lets a stranger in. The few places
where native code does touch them are named:
- **The crypto and SQLite** are on the safety path. That is why what the
  theorems need of them is stated as hypotheses ([What is Assumed](#what-is-assumed)),
  and why they are tested byte for byte against libsodium and the Noise
  test vectors, and row for row against the engine's model, with kill -9
  crashes.
- **Where a tap lands** decides which message it acts on. The hit test
  is proven from the position the shell reports, and removing someone
  takes two confirmations.
- **The text the keyboard hands over** is what gets sent. Lean draws the
  composer from the text it holds, so what is shown before Send is what
  is sent.
- **The control channel** can post as the device, so release builds
  leave it out, and development builds answer only adb (Android) or the
  launch's token (iOS).

**None of the native code is proven:** the proofs take it, and the
libraries under it, as given. It is small, and the goal is to keep
shrinking it: [what else can we move into
Lean?](#what-else-can-we-move-into-lean) lists each decision native code
still makes, how to move it without losing speed, and what that would
let us prove.

| runs on | Lean in the app | our native code | under it |
|---|---|---|---|
| **Android** | 18,376 lines: the engine 10,434, the app 5,657, `engine/renderer/qr/`'s Qr 2,285 | 2,952 lines of C, Java and Rust | SQLite 3.50.4, the Rust crypto crates, and Lean's runtime and libuv 1.51.0 built from source |
| **iOS** | the same | 1,701 lines of C, Objective-C and Rust | the same |
| **the desktop and tests** | the same, and 4,861 lines of tests | 683 lines of C and Rust | the same vendored SQLite and options, the same crates, the toolchain's own runtime |

- Counts are non-blank lines, comments included, and the Lean counts
  include the proofs. With each native file counted once, there are
  4,620 lines in all. `engine/wire/mdns/` (949) and `ops/connection/bootstrap/` (1,385)
  are not in the app.
- The tables below count each file once, under its main job, and name
  the functions in it that do other jobs, with their own counts.
- The builds add 955 lines of shell, and the assets 294 lines of Python
  and shell. They run at build time, not in the app.
- SQLite's amalgamation alone is 246,245 lines of C. Cargo.lock lists
  52 packages besides ours, build-time ones included.
- Paths are the new layout's ([docs/LAYOUT.md](docs/LAYOUT.md)):
  `app/android`, `app/ios` and `app/host` are now `platforms/android`,
  `platforms/ios` and `platforms/headless`.

The lifecycle port also adds an explicit listener close in
[`listener.h`](engine/native/listener.h). After the acceptor joins,
`Runner.stop` invokes the Lean 4.34 UV external object's finalizer once and
replaces its finalizer with a no-op. This depends on the runtime's external
object ABI and UV finalizer, not a Lean proof. A retained-runner test checks
explicit close and repeated stop; the TCP test rebinds the same port while
retaining the stopped runner.

### Each platform's shell

What Lean cannot reach without the OS: why each piece is native, and
what happens if it is wrong.

| | lines | what it does | why it is native | if it is wrong |
|---|---|---|---|---|
| **The Android activity** ([`activity.c`](platforms/android/twin/activity.c), [`activity.h`](platforms/android/twin/activity.h)) | 664 | The NativeActivity's callbacks: the surface, touches, insets and the Java half's events, under one lock. It runs Lean's main on a thread of its own (256 MB of stack), sends stdout to logcat, and copies the APK's assets to the data directory. | Android hands a native app these only through NativeActivity's C callbacks. | The app does not start, or misses an event. The proofs take touches and insets as the OS gave them, in order. |
| **The Java half** ([`LeanActivity.java`](platforms/android/twin/java/com/holmes/leanquiet/LeanActivity.java)) | 312 | The insets at every frame of the keyboard's animation. A hidden EditText holds the composer's text. Send, the clipboard, and the back camera's luma (Camera2). | These APIs are Java's. An EditText is what lets every input method work: autocorrect, dictation, composing CJK. | The composer rides the keyboard badly, or holds other text than was typed, which it then shows. The text, selection and composition Lean reads are the EditText's. |
| **The compositor** ([`layer.c`](platforms/android/twin/layer.c)) | | Four layers, one transaction: Lean supplies placement, painted extent and hold tile; each vsync calls scalar `Slide` exports for translation and fill. | The graphics API and fences are native. | Incorrect pixel copies or API application. `Surface.published_row`, `Translate.equivariance` and `Slide.edge_eq` connect placement to the geometry laws. |
| **Scrolling** ([`scroll.c`](platforms/android/twin/scroll.c), [`scroll.h`](platforms/android/twin/scroll.h)) | 308 | Android's own VelocityTracker and OverScroller through JNI, with the device's ViewConfiguration. | Familiarity: a fling starts, slows and stops as every Android list's does. | A fling feels off. Nothing else: the offset is an input to every theorem, so any offset is drawn correctly. |
| **UIKit** ([`quiet_ios.m`](platforms/ios/quiet_ios.m)) | | IOSurface buffers; a hidden UIScrollView for physics; raw touch/key forwarding; text composition, camera and display link. The visible list uses Lean placement outside that scroll view. | UIKit supplies these OS services. | Incorrect events or pixel/point conversion. CADisplayLink calls the same scalar translation and fill as Android; [`Placement.lean`](platforms/ios/Placement.lean) audits the shared laws. |
| **The control channel** ([`ctl.c`](platforms/android/twin/ctl.c), [`ctl_ios.c`](platforms/ios/ctl_ios.c)) | 510 | The line protocol tests and demos drive the app through; Lean's `App.command` gives each line its meaning. Only in development builds. Android: the abstract socket `@leanquiet`, answering only adb's shell or root. iOS: TCP on 127.0.0.1:7417, behind a token. | Tests drive the real app on a real device and read Lean's state back. | It can act as the device (see [Where native code still decides](#where-native-code-still-decides)); a release build has no listener. |
| **Heap tags off** ([`notag.c`](platforms/android/leanrt/notag.c)) | 10 | Lean's runtime drops a pointer's top byte, which arm64 Android tags, so tagging is turned off before anything allocates. | It must run before Lean's runtime allocates anything. | A crash at start. |
| **The headless twin** ([`host.c`](platforms/headless/host.c)) | 325 | Platform.lean's externs with no OS, driven by a script, with PPM dumps of the screen. | The app's own frame loop runs in tests without a phone. | Tests only; it never ships. |

### Pixels

**Painting is Lean's.** Lean reads and rasterizes pinned Noto TrueType
fonts, including common CJK subsets instanced at Regular (400). A compact
cmap/metric index supports layout before parsing; faces and outlines are
parsed on demand. Unifont remains the fallback, and colour emoji remain
prebuilt QOI pictures. See [Noto rendering](docs/NOTO.md).

The glyph cache has a 4 MiB accounting budget and at most 1,024 entries.
Its insertion and the reader/raster bounds are proved over running Lean
functions. The pure paint API has one memoization seam:
Source.bitmap's compiled equivalence is tested, not proven. Tests compare
every bitmap field and byte with the pure raster, including eviction,
failed reads and concurrent calls. Native allocator/RSS bounds and the
build-time metric index's correspondence are not kernel theorems.

Native code copies the finished rows into the OS's buffers:

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **Into the OS's buffers** (`bl_present` in [`layer.c`](platforms/android/twin/layer.c), `lq_fill_surface` in quiet_ios.m) | 77, 34 | memcpy into an AHardwareBuffer or an IOSurface, waiting a bounded time for one the compositor is not reading. | Nothing. |
| **The window's background** (`lq_paint` in [`quiet_android.c`](platforms/android/twin/quiet_android.c)) | 19 | Fills a new window with the list's background colour, which shows where a slide uncovers rows. | Nothing. |

Two more steps on the way, row reuse and iOS's byte order, are work
Lean could do. They are under
[Where native code still decides](#where-native-code-still-decides).

### Libraries

| | what it gives | what the proofs assume of it |
|---|---|---|
| **The Rust crypto** ([`lib.rs`](engine/native/crypto/src/lib.rs), 145 lines, over ed25519-dalek 3.0.0, curve25519-dalek 5.0.0, chacha20poly1305 0.11.0, sha2 0.10.9 and getrandom 0.3.4) | SHA-256; Ed25519, verified strictly; X25519; the Ed25519 to X25519 conversion; ChaCha20-Poly1305 with Noise's nonce; XChaCha20-Poly1305; the OS's random bytes. One build on every platform. | [`Unforgeable`], [`CollisionFree`], [`NoSecondPreimage`] and [`Suite.Good`] (see Assumed). Tested byte for byte against libsodium ([`crypto_compat.c`](tests/engine/crypto_compat.c)) and against the Noise test vectors. |
| **SQLite** | The store: the vendored 3.50.4 ([`third_party/sqlite`](third_party/sqlite)) on every build, the phones', the desktop's and the tests', with the same options ([`quiet_config.h`](third_party/sqlite/quiet_config.h)). | It behaves like the engine's model ([`Model.lean`](engine/core/Model.lean)). This is tested row for row, with kill -9 crashes and the purge's raw read, on the SQLite the phones ship (`sqlite_build` checks the linked version and options through the externs). |
| **Lean's runtime and libuv** | Reference counting; the ByteArray, String and Array primitives, which are `@[extern]` in Lean's core and implemented in C; tasks and threads; files; clocks; and Std.Async, which gives the TCP runner its sockets ([`Tcp.lean`](engine/wire/Tcp.lean)), mDNS its UDP, and an invite its dial hints (the interface addresses). Phones build it from Lean's source ([`build.sh`](platforms/android/leanrt/build.sh), [`leanrt.sh`](platforms/ios/leanrt.sh)), with no mimalloc and no GMP, OpenSSL stubbed, and libuv compiled from its source lists. | **Lean** in Trusted. The proofs reason about the core's Lean definitions, and the C must match them. The phones' build is not the one the tests run on. |

### FFI glue

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **Platform.lean on Android** ([`quiet_android.c`](platforms/android/twin/quiet_android.c)) | 538 | The 19 externs, including lifecycle polling, OS links and accepted motion samples. Each frame publishes Lean placement and four row arrays (list, header, composer, hold). Touches and lifecycle events come back as eight-word records, the layout `Input.decode` reads. The text, the camera's luma (into a ByteArray), the clipboard, and the local timezone's offset (`lq_tz_min`: `localtime_r`'s `tm_gmtoff`, also in quiet_ios.m and host.c), by which rows show a message's UTC time. A log line (`lq_log`: logcat's "lean" tag, NSLog on iOS, stderr on the host). A watchdog logs a backtrace of Lean's thread if it stalls 3 s. | The words mean what `Input.decode` reads, and the offset is the OS's. |
| **SQLite** ([`glue.c`](engine/native/glue.c)) | 72 | Open, exec, and one statement with blob parameters, every column back as bytes. One file on every platform: the desktop, Android and iOS compile it. | Rows come back as stored. |
| **The crypto** ([`crypto.c`](engine/native/crypto.c)) | 141 | Checks sizes, calls the Rust, and wipes secret bytes from its stack. | Its size rules are decisions of its own (below). |
| **Text** (`ba_utf8` in activity.c, `cp` in LeanActivity.java, `lq_cp` in quiet_ios.m) | 37, 4, 11 | UTF-16 to UTF-8, and the selection and composition in code points, three ways. | The positions index the text Lean gets. |

Lean's side of the seam is every `@[extern]`, each an `opaque` Lean
cannot see into:

| Lean | C | what |
|---|---|---|
| `Engine.sha256` ([`Core.lean`](engine/core/Core.lean)) | `le_sha256` in crypto.c | SHA-256 |
| `Community.edKeypair`, `edSign`, `edVerify` ([`Compose.lean`](ops/community/Compose.lean)) | `le_ed25519_*` in crypto.c | Ed25519 |
| `Engine.Crypto.x25519`, `x25519Base`, `staticOf`, `staticPubOf`, `chachaSeal`, `chachaOpen`, `xchachaSeal`, `xchachaOpen`, `randomBytes` ([`Crypto.lean`](engine/core/Crypto.lean)) | `le_*` in crypto.c | X25519, the key conversion, the two AEADs, random bytes |
| `Engine.Db.open`, `exec` and `query`, over the opaque type `DbPointed` ([`Sqlite.lean`](engine/core/Sqlite.lean)) | `le_sql_*` in glue.c | SQLite |
| The 19 of [`Platform.lean`](engine/renderer/Platform.lean): `screen`, `scroll`, `scrollBy`, `scrollTo`, `frame`, `motion`, `text`, `ime`, `setText`, `copy`, `ctlPoll`, `ctlReply`, `scan`, `luma`, `nowUs`, `tzMin`, `log`, `poll`, `links` | `lq_*` in each shell | OS effects, raw events, placement and pixel publication |
| `register`, `browse`, `poll` ([`NetProbe.lean`](platforms/ios/probe/NetProbe.lean)) | `lq_sd_*` in [`dnssd.c`](platforms/ios/probe/dnssd.c) | DNS-SD, for the iOS network probe only |

- There is no `@[implemented_by]`, no `unsafe` and no `axiom`. The
  other way, `@[export]` gives qr's own Android harness `Qr.decodeLuma`
  (`engine/renderer/qr/Export.lean`) and the picture composer
  (`engine/renderer/pic/Composer.lean`).
- **A pure extern is one fixed function to the logic.** The C under
  `sha256`, the Ed25519 and X25519 functions and the AEADs must be
  deterministic and have no effect. `randomBytes` and the database calls
  are `IO`.
- **Nothing checks the signatures.** Each borrowed argument (`@&`) must
  be a `b_lean_obj_arg` in the C. `le_random` still declares the world
  argument that Lean 4.34 no longer passes; it is unused.

Placement and touch policy now run in Lean: `Surface.make` publishes both
`Seam.place` and `Seam.pinned`; `Input.run` classifies raw pointer sequences
and Enter/IME actions. Native vsync callbacks call `lq_slide_edge`,
`lq_slide_delta`, `lq_slide_source` and `lq_slide_fill_row`, exported by
[`Slide.lean`](engine/renderer/Slide.lean). Their scalar equivalence laws,
coverage contract with main's `Cover`, native thread audit and remaining
trusted operations are in [SEAM.md](docs/SEAM.md). Motion and placeholders
continue between 50 ms Lean frames; fresh data is a separate concern.

### Where native code still decides

This native code does more than carry: it makes decisions, or does work
Lean could do. The proofs do not cover it, and it is first in line to
[move into Lean](#what-else-can-we-move-into-lean).

**Decisions made in native code:**

| | lines | the decision | the proofs |
|---|---|---|---|
| **Scroll physics** (`scroll.c`, UIScrollView) | | Velocity, fling and platform overscroll feel. Lean clamps each new frame; intermediate signed samples translate the last publication without a clamp. | `Input.sequence_offset` bounds frame offsets. `Translate.fill_covers` covers arbitrary interim samples. |
| **Crypto sizes** (crypto.c) | | A ChaCha20-Poly1305 key that is not 32 bytes seals under 32 zero bytes, while opening refuses it. XChaCha20-Poly1305 with a wrong-sized key or nonce seals to empty bytes. A wrong-sized Ed25519 seed gives empty bytes. | [`Suite.Good`] and `Seal.Good` say the AEAD opens what it seals for every key and nonce. The running AEADs do so only for 32-byte keys and 24-byte nonces. |
| **The camera on iOS** (quiet_ios.m) | | The back camera at 1280 × 720, oriented 90° always. Android reads the sensor's own orientation. | [`Camera.src_in`] takes the frame's header as given. |
| **The control channel** (ctl.c and ctl_ios.c, started by activity.c and quiet_ios.m) | | Only development builds have it: `RELEASE=1` builds compile no listener. On Android it is the abstract socket `@leanquiet`, which has no file permissions, so it closes any connection, unread, whose peer (by the kernel's `SO_PEERCRED`) is not adb's shell or root. On iOS it is TCP on 127.0.0.1:7417 (every interface only for a launch with `LEANQUIET_CTL_REMOTE=1`), and a connection's first line must be the launch's 128-bit token. Its commands include `send` (posts as this device), `invite` (the current invite link), `found` and `chaos` (both write ops), and `state` (the composer's text). | Nothing. Another process on the device is not in the model. `android:ctl-guard` and `ios:ctl-guard` test who is answered, with release builds that do not listen. |

- **No protocol decision is native.** The handshake, framing, sync
  rounds, the trust rule and judging are Lean, and the TCP and UDP under
  them are Lean's own Std.Async.
- **Placement is shared:** `Surface` calls Geometry for the frame, and
  the native shells call scalar `Slide` exports between frames. The
  headless raster twin uses those same functions. Graphics API application
  remains native.

**Performance work Lean could do:**

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **Row reuse** (`lq_stage` in quiet_android.c and in quiet_ios.m) | 57, 63 | Copies a frame into a staging buffer. It skips each row that is the same Lean object as the last frame's, at the place the offset's change moves it to. The last frame is held, so a row seen again is the same immutable row. Lean knows which rows it painted, so it could say which are new. | A skipped row holds the same pixels. |
| **Byte order on iOS** (`lq_row` in quiet_ios.m) | 12 | Swizzles every pixel from R G B X to B G R A. Android's buffers take R G B X as it is, so there Lean's rows are copied unchanged. | Nothing. |

No Lean version of these exists, and none was timed for this README. The
Android twin logs its own costs every 120 frames: Lean's time per
frame, the copy's time and rows copied, and the time handing frames over
(`lq_time`). `host:translate` checks every scripted vsync for uncovered
rows and exact motion. The app's host session (`mise run host:app`) reports Lean's
step time and unpainted rows on a fling. The checklist below measures
with these.

### How it is tested

- **On devices, by hand:** `android:twin-demo-e2e`, `android:scan-e2e`,
  `ios:sim-e2e` and `ios:e2e` (mise.toml). `ci/workflow.yml` would
  run the first and the third on self-hosted runners; it is not in use.
- **The app gate runs the native C twin:** `host:twin-demo` drives the
  app through host.c's externs (control replies, keyboard and text, taps,
  send, scrolling, painted pixels; a broken keyboard effect must fail it),
  beside the sessions through `platforms/headless/Sim.lean`'s `Io`.
- **The engine's tests run the crypto and SQLite glue:** against
  libsodium, against the model, through kill -9, the purge's raw read,
  and two nodes over localhost TCP.

### Tested isn't shipped

Desktop tests now link the same SQLite 3.50.4 amalgamation as the phones,
through Lake's `libsqlite` extern library. All three builds include
`third_party/sqlite/quiet_config.h`: `THREADSAFE=2`, `DQS=0`,
`DEFAULT_MEMSTATUS=0`, `OMIT_LOAD_EXTENSION`. All compile the same
`engine/native/glue.c`. The engine gate checks the linked version and
options through the actual externs, then tests differential behavior,
crash atomicity, and secret bytes absent from the database files after
VACUUM and WAL truncate. Controls substitute system SQLite and the wrong
threading mode and must fail.

The app gate now runs `host:twin-demo` through the native C twin's
externs, alongside the app's `Sim` sessions. It checks control replies,
keyboard/text, taps, send, scrolling and painted pixels; disabling the
C keyboard effect must fail it. This does not test a mobile OS.

The ordinary gate still uses Lean's prebuilt runtime. A separate
`test:engine-runtime` task rebuilds Lean's runtime, Init, Std and the
engine suites' generated C for x86_64 Linux with the phone options:
no mimalloc, no GMP, and OpenSSL stubbed. The engine suites pass on that
build too (the socket sandbox omits `tcppair` and `jointcp`). It still
uses Linux libc/libuv and the desktop compiler, not Android's NDK/libc
or iOS's Darwin runtime, `system()` stub and thread-stack settings.
The mobile suites are needed to test those remaining differences.

The Android emulator and iOS Simulator suites have build-and-run mise
tasks and manual/nightly jobs in `ci/workflow.yml`, retaining failure
logs, screenshots and the iOS result bundle. That workflow is inactive
today; adding jobs records intent, not a mobile test result.
[docs/SHIPPED.md](docs/SHIPPED.md) gives the machines, commands and
artifact paths.

- [x] The desktop suites use the shipped SQLite version and options.
- [x] Desktop, Android and iOS share one SQLite glue file.
- [x] The native C twin runs in the app gate, with a negative control.
- [x] The phone runtime options are tested by the engine suites on Linux.
- [x] Mobile suites include builds and retain failure artifacts; their
  provisioned-machine jobs are recorded as manual/nightly runs.
- [x] Run the blocked TCP suites outside the sandbox (`SKIP_TCP` unset).
- [ ] Run the new builds on the provisioned emulator and Simulator, and
  activate the workflow for continuing mobile coverage. No phone,
  emulator, Simulator or Mac was used to validate this change.

## What else can we move into Lean?

**The goal is for Lean to make every decision the app makes**, and for
native code to do only what the OS alone can: hand over input, host the
layers, run the platform's keyboard and scroll physics, and copy bytes.
Every decision that moves is one more thing the proofs can reach. Each
item says what moves, what replaces it, how to keep it as fast, and what
it would let us prove.

The first three seam changes are now implemented; the remaining items move
more OS policy or library work into Lean.

- [x] **Decide phone taps and keys in Lean.** `Input.run` consumes raw
  pointers, timestamps, keys and IME actions; first-pointer ownership,
  slop, long press and content mapping are shared with the twin.
- [x] **Call the placement.** `Surface.make` publishes list, header and
  composer rectangles. Native vsyncs call scalar `Slide` exports for
  translation and placeholder fill. Generated C and assembly are audited
  for objects, once-cells and calls; native threads initialize once.
- [x] **Bound frame offsets in Lean.** `Input.sampleOffset` clamps OS
  samples before painting. Between frames, arbitrary signed OS samples
  translate the last buffer with complete placeholder coverage. Native
  scroll physics remains the OS's. See [SEAM.md](docs/SEAM.md).
- [ ] **The control channel in Lean, and off unless asked.**
  - Today: only development builds have it, and it answers only adb or
    root (Android) or the launch's token (iOS).
  - Moves: ctl.c and ctl_ios.c (510 lines).
  - Instead: a listener on 127.0.0.1 in Lean (Std.Async's TCP), started
    only when the launch asks for it. Android reaches it with `adb
    forward tcp:N tcp:M`. iOS's `twin` report stays an extern.
  - Speed: nothing to lose; it serves tests.
  - Then provable: an app launched without the flag reads no command,
    as a statement about `App.start`.
- [ ] **Sizes as types in the crypto.**
  - Moves: crypto.c's size checks and its fallbacks (the zero key, the
    empty results).
  - Instead: fixed-size byte types in `Engine.Crypto` (32-byte keys,
    24-byte nonces), so crypto.c passes pointers it never checks.
  - Speed: the same either way.
  - Then provable: [`Suite.Good`] and `Seal.Good`, as stated, of the
    AEADs that run.
- [ ] **Decide row reuse in Lean.**
  - Moves: the row comparison in both twins' `lq_stage` (57 and 63
    lines).
  - Instead: each frame carries its shift and which rows are new, which
    Lean knows because it painted them. The twin moves its buffer by
    the shift and copies the listed rows.
  - Speed: the same copies as today. Compare `lq_time`'s copy time and
    rows copied on the same fling before and after; compare
    host.c's dumps byte for byte.
  - Then provable: the staging buffer equals the frame Lean drew, the
    first step of the wanted "content is drawn faithfully all the way to
    pixels".
- [ ] **Paint in the platform's byte order.**
  - Moves: iOS's per-pixel swizzle (`lq_row`, 12 lines).
  - Instead: Paint writes B G R A on iOS, so the twin copies rows with
    memcpy, as Android's does.
  - Speed: Lean writes the same bytes in another order, and the twin's
    loop goes. Compare the app's `stats` (Lean's frame time) and the
    screenshots, before and after.
  - Then provable: the bytes the compositor reads are the bytes Lean
    painted.
- [ ] **Report the iOS camera's orientation; don't assume it.**
  - Moves: quiet_ios.m's fixed 90°.
  - Instead: the orientation AVFoundation gives for the frames, as
    Android's twin reads the sensor's.
  - Speed: nothing changes.
  - Then provable: nothing new, but [`Camera.src_in`]'s input is then
    the OS's, not a guess.
- [ ] **Decode the keyboard's text in Lean.**
  - Moves: `ba_utf8` (activity.c), `cp` (LeanActivity.java) and `lq_cp`
    (quiet_ios.m).
  - Instead: the twin hands over the UTF-16 code units and UTF-16
    offsets, and Lean decodes them and converts the offsets.
  - Speed: the text is short, and changes once a keystroke.
  - Then provable: the selection and the composition are positions in
    the text Lean holds, with one rule for an unpaired surrogate on
    every platform.
- [ ] **Scroll physics in Lean.**
  - Moves: scroll.c's VelocityTracker and OverScroller calls, and on
    iOS the UIScrollView's deceleration and bounce.
  - Instead: Android's physics needs no reverse engineering:
    VelocityTracker, OverScroller and ViewConfiguration are AOSP's own
    open source, so their curves and constants can be ported and
    checked against the platform's, fling by fling. iOS publishes its
    deceleration rates (`UIScrollView.DecelerationRate`); the rest (the
    rubber band, the hand-off from drag to fling) is measured from
    recordings and matched. The twins then report only touches and
    vsyncs.
  - Speed: a few multiply-adds a vsync, on the vsync thread, as for the
    placement. The risk is feel, not speed: a fling that is almost
    native feels wrong, so it is matched against the platform's own on
    the same touches before it ships.
  - Then provable: the offset never leaves the content's range, a fling
    slows steadily and stops where it was predicted to, and the
    prediction Lean draws at is the offset shown.

**What stays native:**
- **The OS's own APIs:** the window and the compositor (ASurfaceControl
  and AHardwareBuffer; IOSurface and Core Animation), vsync, touches as
  the OS delivers them, the keyboard (an EditText and a UITextField, so
  every input method works), the camera, the clipboard, permissions and
  the app's lifecycle, logging, and the last copy into the OS's buffers.
  Scrolling's physics stays the OS's for now, so a fling feels native,
  as LAYOUT.md has it (the last item above would move it).
- **Vetted crypto:** the Rust crates, their hypotheses kept as
  hypotheses.
- **SQLite, tested as it ships.** One vendored SQLite, with the phones'
  options, and one glue.c on every platform, so the engine's
  differential, crash and purge tests run what ships.
- **Lean's runtime and libuv,** with the phones' builds of them run by
  tests too.

## Layout

One Lake package, laid out as [docs/LAYOUT.md](docs/LAYOUT.md) says:
the engine for everything that holds for every op type, ops by family
and domain, and platforms by name. A module's name is its path
(`engine/core/Codec.lean` is `engine.core.Codec`); namespaces are the
code's own (`Engine`, `Community`, `Connection`, …).

| directory | what |
|---|---|
| `engine/core/` | the op engine: codec, ids, judging, the store (SQLite and held), lists, purge |
| `engine/wire/` | frames, the node and its TCP runner, and mDNS/DNS-SD discovery (`mdns/`) |
| `engine/renderer/` | the app's rows, text, images and paint, the platform seam, QR encoding and decoding (`qr/`) and pictures (`pic/`) |
| `engine/native/` | the C glue and the Rust crypto (`crypto/`) |
| `ops/sync/` | sync's rounds, fingerprints and connection, and their laws |
| `ops/connection/` | the Connection family (the handshake and sessions), and the bootstrap's model and its laws (`bootstrap/`) |
| `ops/community/` | the Community family and its laws, and each domain's view (`message/`, `profile/`, `reaction/`, `attachment/`, `membership/`, `link/`) |
| `ops/app/` | the app's own state: pages, composer, switcher, removal, and the chaos generator |
| `App.lean` | the root component; `Main.lean` runs it on a platform, and `Quiet.lean` imports every module of the app |
| `platforms/` | the Android and iOS shells, and the headless twin with the programs the tests drive (`headless/`) |
| `tests/` | the axiom audit (`Axioms.lean`) and its gate (`check.sh`), and each part's suites (`engine/`, `app/`, `qr/`, `mdns/`, `net/`) |
| `docs/` | the layout, sync's design, the engine, QR, mDNS and bootstrap notes, building for phones |
| `tools/`, `third_party/` | asset and test tools; the vendored SQLite |

The gates are mise tasks (`mise tasks` lists every task):
- `mise run check`: every library builds, and every law of
  `tests/Axioms.lean` rests on the standard axioms;
- `mise run test:engine`, `test:app`, `test:qr`, `test:mdns` and
  `test:net`: each part's suites (`tests/<part>/`);
- `mise run readme:links`: the README's theorem links match the code.

CI runs locally for now:
- `ci/local.sh` runs every gate, or `ci/local.sh check app` for some
  (its parts: check, engine, mdns, qr, net, app, readme, reorg). Logs
  go to `out/ci/`. `mise run ci` runs it.
- `ci/workflow.yml` is the same for a hosted runner, and is not in use.

Sync's design is [docs/SYNC.md](docs/SYNC.md).

Each part's history is its former repository's (lean-engine,
lean-quiet, lean-qr, lean-mdns, lean-net), rewritten into its directory
and then moved into this layout (`git log --follow` follows a file).
Their other branches are kept as `import/<dir>/<branch>`. A branch begun
on the old layout comes over with `ci/reorg-map.tsv` (where each file
went) and `ci/reorg-imports.py` (its new files' imports).

<!-- proof-links: written by ci/proof-links.py; do not edit -->
[`stream_delivers`]: engine/wire/WorldLaws.lean#L788-L821
[`same_ops_same_verdicts`]: engine/core/Termination.lean#L118-L126
[`Unforgeable`]: ops/community/Laws.lean#L279-L281
[`CollisionFree`]: engine/core/Proofs.lean#L542-L544
[`Distinct`]: engine/core/Proofs.lean#L538-L540
[`lbl_inj`]: ops/sync/Fp.lean#L264-L268
[`NoSecondPreimage`]: ops/community/Merkle.lean#L146-L147
[`assumptions_hold`]: ops/community/Merkle.lean#L543-L547
[`Suite.Good`]: ops/connection/Noise.lean#L61-L65
[`no_impersonation`]: ops/community/Laws.lean#L298-L311
[`admission_needs_approval`]: ops/community/Laws.lean#L478-L486
[`admission_approved`]: ops/community/Laws.lean#L397-L407
[`request_invited`]: ops/community/Laws.lean#L361-L371
[`removal_authorized`]: ops/community/Laws.lean#L526-L529
[`admin_granted`]: ops/community/Laws.lean#L565-L566
[`removed_stays`]: ops/community/Laws.lean#L572-L575
[`valid_stays`]: ops/community/Laws.lean#L579-L583
[`message_authorized`]: ops/community/Laws.lean#L264-L270
[`approval_signed`]: ops/community/Laws.lean#L380-L390
[`invitation_issued`]: ops/community/Laws.lean#L346-L352
[`named_by_admin`]: ops/community/Laws.lean#L617-L619
[`admission_consented`]: ops/community/Laws.lean#L283-L289
[`admin_removal_stands`]: ops/community/Laws.lean#L537-L550
[`mutual_removal`]: ops/community/Laws.lean#L558-L562
[`removed_approver_admits`]: ops/community/Laws.lean#L497-L508
[`recv_send`]: ops/sync/ConnLaws.lean#L154-L156
[`hold_reply_local`]: ops/sync/OfferLaws.lean#L635-L645
[`heldIn_index`]: ops/sync/OfferLaws.lean#L657-L660
[`hold_reply_local_premises`]: ops/sync/OfferLaws.lean#L683-L687
[`onWant_authorized`]: ops/sync/ServeLaws.lean#L282-L285
[`serveOwed_blind`]: ops/sync/ServeLaws.lean#L469-L473
[`serveOwed_shown`]: ops/sync/ServeLaws.lean#L451-L457
[`offer_shared`]: ops/sync/SecrecyLaws.lean#L60-L64
[`wire_kinds`]: ops/connection/Laws.lean#L48-L49
[`local_kinds`]: ops/connection/Laws.lean#L55-L56
[`joinOps_travels`]: ops/community/Intents.lean#L382-L386
[`found_travels`]: ops/community/Intents.lean#L400-L406
[`stopWaiting_local`]: ops/community/Intents.lean#L389-L390
[`filed_send`]: ops/sync/ConnLaws.lean#L185-L188
[`offer_stored`]: ops/sync/SecrecyLaws.lean#L78-L82
[`tick_send`]: ops/sync/ConnLaws.lean#L211-L213
[`recipients_iff`]: ops/community/Connect.lean#L324-L329
[`members_iff`]: ops/community/Connect.lean#L314-L316
[`member_opens`]: ops/community/Laws.lean#L937-L941
[`openSealed_seal`]: ops/community/Laws.lean#L927-L929
[`unbox_box`]: ops/community/Keys.lean#L89-L91
[`check_reads_shared`]: ops/community/Laws.lean#L848-L850
[`kk_secret`]: ops/connection/NoiseSymbolic.lean#L595-L609
[`kk_secret_init`]: ops/connection/NoiseSymbolic.lean#L547-L556
[`kk_secret_resp`]: ops/connection/NoiseSymbolic.lean#L561-L569
[`kk_authentic`]: ops/connection/NoiseSymbolic.lean#L806-L820
[`kk_authentic_resp`]: ops/connection/NoiseSymbolic.lean#L872-L885
[`kk_secret_init_tight`]: ops/connection/NoiseSymbolic.lean#L616-L625
[`kk_runs`]: ops/connection/NoiseSymbolic.lean#L304-L312
[`handshake_agrees`]: ops/connection/Noise.lean#L308-L320
[`close_purges`]: engine/wire/CloseLaws.lean#L34-L42
[`close_gone`]: engine/wire/CloseLaws.lean#L21-L25
[`drop_iff_silent`]: ops/sync/TimeLaws.lean#L22-L24
[`keepalive_sent`]: ops/sync/TimeLaws.lean#L31-L35
[`live_stays`]: ops/sync/TimeLaws.lean#L73-L88
[`kk_forward_secret`]: ops/connection/NoiseSymbolic.lean#L685-L696
[`purge_named`]: engine/core/Purge.lean#L267-L271
[`have_shown`]: ops/sync/OfferLaws.lean#L529-L541
[`boot_cached`]: engine/wire/NodeLaws.lean#L259-L260
[`write_cached`]: engine/wire/NodeLaws.lean#L436-L440
[`purge_cached`]: engine/wire/NodeLaws.lean#L508-L513
[`cached_items`]: engine/wire/NodeLaws.lean#L271-L274
[`write_snaps`]: ops/sync/OfferLaws.lean#L585-L588
[`have_shown_premises`]: ops/sync/OfferLaws.lean#L676-L680
[`opened_endpoint`]: ops/connection/RemovalLaws.lean#L295-L303
[`established_endpoint`]: ops/connection/RemovalLaws.lean#L320-L333
[`endpoint_signed`]: ops/community/RemovalLaws.lean#L44-L51
[`endpoint_derives`]: ops/community/RemovalLaws.lean#L91-L93
[`meV_node`]: ops/connection/RemovalLaws.lean#L383-L388
[`new_device_trusted`]: ops/community/RemovalLaws.lean#L100-L106
[`connect_iff`]: ops/community/Connect.lean#L252-L256
[`deviceLive_iff`]: ops/community/Connect.lean#L135-L139
[`refuse_nonmember`]: ops/community/Connect.lean#L267-L270
[`connect_approved`]: ops/community/Connect.lean#L290-L302
[`connect_agree`]: ops/community/Connect.lean#L337-L340
[`removal_cuts_off`]: ops/community/Connect.lean#L352-L359
[`cut_stays`]: ops/community/RemovalLaws.lean#L60-L63
[`cut_consented`]: ops/community/RemovalLaws.lean#L68-L75
[`removals_iff`]: ops/community/Connect.lean#L49-L50
[`mine_not_removed`]: ops/community/RemovalLaws.lean#L385-L389
[`rejoin_fresh`]: ops/community/RemovalLaws.lean#L432-L445
[`join_new_device`]: ops/community/RemovalLaws.lean#L475-L482
[`removed_stays_removed`]: ops/community/RemovalLaws.lean#L519-L529
[`rejoin_dials`]: ops/connection/RemovalLaws.lean#L1153-L1166
[`reconnect_dials`]: ops/connection/RemovalLaws.lean#L1178-L1188
[`rooms_cut_node`]: ops/connection/NodeLaws.lean#L187-L199
[`rooms_trusted`]: ops/connection/RoomLaws.lean#L100-L107
[`rooms_cut`]: ops/connection/RoomLaws.lean#L120-L131
[`rooms_removed`]: ops/connection/RemovalLaws.lean#L96-L101
[`rooms_complete`]: ops/connection/RemovalLaws.lean#L121-L127
[`notice_then_cut`]: ops/connection/RemovalLaws.lean#L253-L266
[`trusts_live`]: ops/connection/RoomLaws.lean#L45-L51
[`rooms_model`]: ops/connection/RoomLaws.lean#L137-L140
[`recv_take`]: ops/sync/ConnLaws.lean#L125-L127
[`notice_sent`]: ops/sync/NoticeLaws.lean#L576-L587
[`closure`]: ops/sync/NoticeLaws.lean#L281-L289
[`notice_send`]: ops/sync/NoticeLaws.lean#L609-L616
[`removed_gets_only_notice`]: ops/connection/RemovalLaws.lean#L133-L144
[`notice_once`]: ops/sync/NoticeLaws.lean#L641-L647
[`notice_no_holds`]: ops/sync/NoticeLaws.lean#L436-L447
[`answer_trusted`]: ops/connection/RemovalLaws.lean#L842-L855
[`resend_trusted`]: ops/connection/RemovalLaws.lean#L921-L932
[`no_connection_before_approval`]: ops/connection/bootstrap/Laws.lean#L39-L46
[`sessions_trusted`]: ops/connection/bootstrap/Laws.lean#L63-L68
[`bare_takes_only_join`]: ops/connection/RemovalLaws.lean#L612-L624
[`intake_local`]: engine/core/Sync.lean#L38-L40
[`stored_local`]: engine/core/Sync.lean#L86-L89
[`local_fact_mine`]: ops/community/Laws.lean#L636-L640
[`intakeConn_conn`]: engine/core/Sync.lean#L33-L34
[`established_agrees`]: ops/connection/Laws.lean#L59-L73
[`open_seal`]: ops/connection/Frame.lean#L51-L55
[`cid_seal`]: ops/connection/Frame.lean#L79-L82
[`Codec.encode_decode`]: engine/core/Codec.lean#L743-L746
[`Op.id_decode`]: engine/core/Core.lean#L89-L91
[`distinct_of_collisionFree`]: engine/core/Proofs.lean#L546-L549
[`op_of_valid`]: ops/community/Laws.lean#L236-L241
[`Pic.decode_sized`]: engine/renderer/pic/Laws.lean#L198-L201
[`Image.decode_sized`]: engine/renderer/ImageLaws.lean#L11-L14
[`Mdns.decode_valid`]: engine/wire/mdns/Laws.lean#L540-L541
[`Community.parse_valid`]: ops/community/Link.lean#L214-L215
[`Qr.parse_valid`]: engine/renderer/qr/SegLaws.lean#L336-L338
[`chunk_is_slice`]: ops/community/Laws.lean#L682-L691
[`verify_sound`]: ops/community/Merkle.lean#L435-L441
[`complete_assembles`]: ops/community/Merkle.lean#L482-L488
[`chunk_unique`]: ops/community/Laws.lean#L772-L778
[`progress_exact`]: ops/community/Intents.lean#L713-L722
[`no_injective_hash`]: ops/community/Merkle.lean#L245-L247
[`drain_bounded`]: engine/core/Budget.lean#L163-L168
[`drain_terminates`]: engine/core/Termination.lean#L84-L87
[`step_budget`]: engine/core/Budget.lean#L124-L126
[`sealed_auth`]: ops/connection/Laws.lean#L191-L202
[`openFrame_auth`]: ops/connection/Laws.lean#L143-L150
[`onFrame_sealed`]: engine/wire/NodeLaws.lean#L52-L58
[`sealed_unopened`]: engine/wire/NodeLaws.lean#L67-L73
[`buffer_bounded`]: engine/wire/Frame.lean#L213-L218
[`frames_kept`]: engine/wire/Frame.lean#L158-L161
[`frames_tooBig`]: engine/wire/Frame.lean#L180-L183
[`admit_bounded`]: engine/wire/Slots.lean#L69-L74
[`Op.decode_exact`]: engine/core/Core.lean#L96-L98
[`Op.decode_parts`]: engine/core/Core.lean#L101-L104
[`decode_sum`]: engine/core/Codec.lean#L779-L782
[`hold_bounded`]: ops/sync/BoundsLaws.lean#L57-L58
[`conn_bounded`]: ops/sync/BoundsLaws.lean#L222-L223
[`conn_state_bounded`]: ops/sync/StateLaws.lean#L159-L163
[`full_round_stateless`]: ops/sync/ClosureLaws.lean#L73-L77
[`closure_capped`]: ops/sync/ClosureLaws.lean#L42-L44
[`closure_complete_under_cap`]: ops/sync/ClosureComplete.lean#L234-L242
[`honest_no_drop`]: ops/sync/RetryLaws.lean#L102-L106
[`work_retry_bounded`]: ops/sync/RetryLaws.lean#L172-L173
[`serveOwed_budget`]: ops/sync/ServeLaws.lean#L441-L443
[`asks_expire`]: ops/sync/RetryLaws.lean#L129-L131
[`room_independent`]: ops/sync/TimeLaws.lean#L136-L142
[`unshown_room_answered`]: ops/sync/TimeLaws.lean#L130-L133
[`uncarried_room_answered`]: ops/sync/TimeLaws.lean#L147-L153
[`purges_notified`]: engine/wire/CloseLaws.lean#L57-L62
[`flush_notifies`]: engine/wire/CloseLaws.lean#L66-L69
[`order_free`]: engine/core/Proofs.lean#L634-L639
[`drain_settles`]: engine/core/Termination.lean#L110-L114
[`status_iff_spec`]: engine/core/Proofs.lean#L483-L485
[`spec_extends`]: engine/core/SpecLemmas.lean#L137-L139
[`inv_ingest`]: engine/core/Proofs.lean#L229-L229
[`inv_step`]: engine/core/Proofs.lean#L260-L260
[`ingestS_known`]: engine/core/IdemLaws.lean#L22-L23
[`ingestS_twice`]: engine/core/IdemLaws.lean#L44-L45
[`ingest_twice`]: engine/core/IdemLaws.lean#L49-L51
[`run_ingestEach`]: engine/core/IdemLaws.lean#L72-L75
[`ingestAll_again`]: engine/core/IdemLaws.lean#L82-L84
[`purge_gone`]: engine/core/Purge.lean#L261-L263
[`purge_shared`]: engine/core/Purge.lean#L274-L276
[`purge_settles`]: engine/core/Budget.lean#L192-L198
[`purge_undecides`]: engine/core/Proofs.lean#L376-L383
[`purge_inv`]: engine/core/Proofs.lean#L391-L395
[`mem_purgeSet`]: engine/core/Proofs.lean#L364-L368
[`reach_ops`]: engine/core/Proofs.lean#L624-L626
[`sum_left`]: engine/core/Families.lean#L79-L82
[`sum_scope_left`]: engine/core/Families.lean#L85-L86
[`Codec.decode_encode`]: engine/core/Codec.lean#L737-L737
[`Op.decode_bytes`]: engine/core/Core.lean#L94-L94
[`sum_project`]: engine/core/Project.lean#L421-L432
[`sum_project_node`]: ops/connection/NodeLaws.lean#L106-L117
[`spec_sum_left`]: engine/core/Project.lean#L195-L198
[`view_proj`]: engine/core/Project.lean#L408-L411
[`connect_iff_node`]: ops/connection/NodeLaws.lean#L147-L152
[`members_iff_node`]: ops/connection/NodeLaws.lean#L172-L175
[`recipients_iff_node`]: ops/connection/NodeLaws.lean#L179-L183
[`node_settles`]: ops/connection/NodeLaws.lean#L206-L210
[`request_valid`]: ops/community/Laws.lean#L418-L426
[`approve_valid`]: ops/community/Laws.lean#L434-L442
[`admit_admits`]: ops/community/Laws.lean#L450-L461
[`connect_admitted`]: ops/community/Connect.lean#L276-L286
[`removeMember_valid`]: ops/community/Intents.lean#L579-L586
[`exchange_complete`]: ops/sync/RoundLaws.lean#L232-L241
[`opening_honest`]: ops/sync/RoundLaws.lean#L323-L325
[`num_inj`]: ops/sync/Fp.lean#L37-L37
[`spec_local`]: engine/core/Locality.lean#L54-L58
[`bootstrap`]: ops/connection/bootstrap/Laws.lean#L401-L405
[`bootstrap_ideal`]: ops/connection/bootstrap/Laws.lean#L423-L424
[`bootstrap_possible`]: ops/connection/bootstrap/Laws.lean#L208-L218
[`reachable_inv`]: ops/connection/bootstrap/Steps.lean#L222-L223
[`conn_answers_ids`]: engine/wire/WorldLaws.lean#L1492-L1514
[`stream_offered`]: engine/wire/WorldLaws.lean#L1438-L1450
[`stream_delivers_steps`]: engine/wire/WorldLaws.lean#L826-L843
[`stream_offered_runs`]: engine/wire/WorldLaws.lean#L1457-L1463
[`stream_delivers_runs`]: engine/wire/WorldLaws.lean#L873-L878
[`onWant_all`]: ops/sync/ServeLaws.lean#L297-L301
[`onWant_order`]: ops/sync/ServeLaws.lean#L316-L319
[`serveOwed_head`]: ops/sync/ServeLaws.lean#L382-L387
[`serveOwed_fifo`]: ops/sync/ServeLaws.lean#L392-L393
[`owed_within`]: ops/sync/ServeLaws.lean#L430-L438
[`want_sends`]: engine/wire/WorldLaws.lean#L625-L635
[`write_first`]: engine/wire/LaneLaws.lean#L267-L270
[`write_within`]: engine/wire/LaneLaws.lean#L290-L294
[`urgent_ahead`]: engine/wire/LaneLaws.lean#L100-L109
[`ahead_bytes`]: engine/wire/LaneLaws.lean#L169-L184
[`cut_bytes`]: engine/wire/LaneLaws.lean#L59-L61
[`push_capped`]: engine/wire/LaneLaws.lean#L126-L130
[`serveOwed_hot`]: ops/sync/ServeLaws.lean#L374-L378
[`hot_ids`]: engine/wire/LaneLaws.lean#L323-L326
[`lane_control`]: engine/wire/LaneLaws.lean#L312-L315
[`fresh_served`]: engine/wire/WorldLaws.lean#L613-L620
[`write_hot`]: engine/wire/WorldLaws.lean#L1424-L1429
[`unmount_read`]: ops/app/LifecycleLaws.lean#L12-L14
[`unmount_write`]: ops/app/LifecycleLaws.lean#L16-L18
[`old_callback`]: ops/app/LifecycleLaws.lean#L20-L22
[`unmounted_quiet`]: ops/app/Lifecycle.lean#L66-L67
[`old_quiet`]: ops/app/Lifecycle.lean#L70-L71
[`live_exact`]: ops/app/Lifecycle.lean#L86-L90
[`subscriptions_exact`]: ops/app/Lifecycle.lean#L74-L75
[`mounted_runs`]: ops/app/Lifecycle.lean#L139-L141
[`restore_checkpoint`]: ops/app/Lifecycle.lean#L136-L136
[`page_round`]: AppLife.lean#L24-L24
[`restore_page_anchor`]: ops/app/LifecycleLaws.lean#L28-L34
[`apply_page_anchor`]: ops/app/LifecycleLaws.lean#L38-L43
[`resize_anchor`]: ops/app/Lifecycle.lean#L104-L105
[`viewport_geometry`]: ops/app/LifecycleLaws.lean#L54-L58
[`viewport_possible`]: ops/app/LifecycleLaws.lean#L61-L62
[`Surface.visible_in_viewport`]: engine/renderer/Surface.lean#L123-L127
[`newest_visible`]: engine/renderer/Geometry.lean#L101-L107
[`Surface.pinned_visible`]: engine/renderer/Surface.lean#L141-L143
[`pinned_tap`]: engine/renderer/Geometry.lean#L156-L159
[`hit_iff`]: engine/renderer/SheetGeom.lean#L124-L126
[`offer_split`]: ops/app/NodeOffer.lean#L37-L40
[`offer_runs`]: ops/app/NodeOffer.lean#L73-L77
[`eval_stable`]: engine/core/View.lean#L137-L142
[`view_stable`]: engine/core/View.lean#L163-L165
[`filed_rel`]: engine/core/Decl.lean#L189-L196
[`mem_keysOf`]: engine/core/Decl.lean#L79-L82
[`matching_nodup`]: engine/core/Decl.lean#L158-L161
[`notice_iff`]: engine/core/WindowLaws.lean#L698-L706
[`read_notice_iff`]: engine/core/WindowRead.lean#L408-L420
[`read_rows_iff`]: engine/core/WindowRead.lean#L284-L290
[`Engine.window_rows`]: engine/core/WindowRead.lean#L357-L362
[`watch_stable`]: engine/core/WindowRead.lean#L446-L453
[`run_exact`]: engine/core/WindowLaws.lean#L428-L433
[`fact_stable`]: engine/core/WindowLaws.lean#L509-L515
[`find_costs`]: engine/core/WindowCost.lean#L133-L137
[`notify_cost`]: engine/core/WindowCost.lean#L195-L198
[`screen_subs`]: engine/renderer/Screen.lean#L130-L139
[`hull_near`]: engine/renderer/Screen.lean#L216-L220
[`past_hull_le`]: engine/renderer/Screen.lean#L270-L280
[`key_notice_imprecise`]: engine/core/WindowMutants.lean#L110-L113
[`unnetted_imprecise`]: engine/core/WindowMutants.lean#L160-L164
[`keep_scrolled_off`]: engine/renderer/Screen.lean#L319-L324
[`agrees_notice`]: engine/renderer/LiveLaws.lean#L139-L144
[`agrees_unmount`]: engine/renderer/LiveLaws.lean#L182-L188
[`watched_held`]: engine/renderer/LiveLaws.lean#L194-L198
[`writes_only_after_two`]: ops/app/Remove.lean#L56-L59
[`cancel_writes_nothing`]: ops/app/Remove.lean#L63-L64
[`open_fresh`]: ops/app/Remove.lean#L67-L69
[`no_replace`]: ops/app/Remove.lean#L74-L76
[`offered_only`]: ops/app/Remove.lean#L83-L86
[`back_go`]: engine/renderer/Nav.lean#L94-L96
[`NavLaws.back_open`]: ops/app/NavLaws.lean#L29-L31
[`NavLaws.back_root`]: ops/app/NavLaws.lean#L37-L39
[`back_switch`]: ops/app/NavLaws.lean#L54-L57
[`go_inv`]: engine/renderer/Nav.lean#L107-L107
[`NavLaws.depth`]: ops/app/NavLaws.lean#L82-L84
[`draft_back`]: ops/app/NavLaws.lean#L65-L67
[`into_native`]: App.lean#L129-L132
[`present_iff`]: ops/app/PeopleLaws.lean#L28-L31
[`present_not_removed`]: ops/app/PeopleLaws.lean#L38-L41
[`present_nodup`]: ops/app/PeopleLaws.lean#L45-L46
[`read_one_moment`]: engine/renderer/LiveLaws.lean#L200-L205
[`answer_agrees`]: engine/renderer/LiveLaws.lean#L81-L83
[`agrees_store`]: engine/renderer/LiveLaws.lean#L92-L95
[`agrees_keep`]: engine/renderer/LiveLaws.lean#L172-L174
[`agrees_empty`]: engine/renderer/LiveLaws.lean#L78-L78
[`Cover.covered`]: engine/renderer/Cover.lean#L81-L86
[`Cover.line_painted`]: engine/renderer/Cover.lean#L122-L125
[`Translate.covered`]: engine/renderer/TranslateLaws.lean#L81-L88
[`Translate.equivariance`]: engine/renderer/TranslateLaws.lean#L12-L14
[`Translate.fill_pixel`]: engine/renderer/TranslateLaws.lean#L143-L149
[`Slide.edge_eq`]: engine/renderer/SlideLaws.lean#L126-L130
[`Surface.placed_row`]: engine/renderer/Surface.lean#L119-L120
[`Surface.newest_drawn`]: engine/renderer/Surface.lean#L146-L149
[`Surface.pinned_row`]: engine/renderer/Surface.lean#L137-L138
[`keys_disjoint`]: engine/renderer/SheetGeom.lean#L179-L181
[`hit_cell`]: engine/renderer/SheetGeom.lean#L175-L177
[`reachable`]: engine/renderer/SheetGeom.lean#L196-L199
[`itemAt_place`]: engine/renderer/SheetGeom.lean#L88-L90
[`lineOf_ctop`]: engine/renderer/SheetGeom.lean#L97-L101
[`chips_apart`]: ops/app/Composer.lean#L66-L69
[`x_clear`]: ops/app/Composer.lean#L75-L78
[`chips_fit`]: ops/app/Composer.lean#L86-L91
[`compose_row`]: engine/renderer/SheetGeom.lean#L220-L224
[`compose_top`]: engine/renderer/SheetGeom.lean#L230-L233
[`Link.hints_fit`]: ops/community/link/View.lean#L49-L51
[`Link.qr_fits`]: ops/community/link/View.lean#L67-L67
[`Camera.src_in`]: engine/renderer/Camera.lean#L51-L53
[`wrap_keeps`]: engine/renderer/WrapLaws.lean#L132-L135
[`wrap_fits`]: engine/renderer/WrapLaws.lean#L206-L209
[`visual_perm`]: engine/renderer/TextLaws.lean#L20-L21
[`place_shows`]: engine/renderer/TextLaws.lean#L36-L38
[`place_starts`]: engine/renderer/TextLaws.lean#L115-L121
[`numbers_keep_order`]: engine/renderer/TextLaws.lean#L84-L88
[`arabic_numbers_keep_order`]: engine/renderer/TextLaws.lean#L91-L94
[`message_read`]: ops/community/message/ViewLaws.lean#L62-L67
[`profile_read`]: ops/community/message/ViewLaws.lean#L40-L42
[`profile_authorized`]: ops/community/Laws.lean#L316-L323
[`no_renaming`]: ops/community/Laws.lean#L330-L341
[`name_placed`]: ops/community/reaction/RowLaws.lean#L89-L92
[`oneLine_prefix`]: engine/renderer/TextLaws.lean#L70-L71
[`controls_neutral`]: engine/renderer/TextLaws.lean#L140-L143
[`marks_invisible`]: engine/renderer/TextLaws.lean#L145-L145
[`namesake_iff`]: ops/community/profile/NamesakeLaws.lean#L113-L118
[`row_marked`]: ops/community/profile/NamesakeLaws.lean#L139-L144
[`twin_shown`]: ops/community/reaction/RowLaws.lean#L131-L135
[`twin_before_time`]: ops/community/reaction/RowLaws.lean#L138-L142
[`hit_twin`]: ops/community/reaction/RowLaws.lean#L152-L154
[`name_starts`]: ops/community/reaction/RowLaws.lean#L122-L125
[`flush_shows`]: ops/community/reaction/RowLaws.lean#L97-L98
[`Ttf.byte_in_bounds`]: engine/renderer/Ttf/Laws.lean#L11-L12
[`Ttf.cmap_entry`]: engine/renderer/Ttf/Laws.lean#L18-L19
[`Ttf.coverage_value`]: engine/renderer/Ttf/Laws.lean#L43-L44
[`Ttf.raster_valid`]: engine/renderer/Ttf/Laws.lean#L60-L61
[`Ttf.raster_pixel`]: engine/renderer/Ttf/Laws.lean#L69-L73
[`Ttf.Cache.put_bound`]: engine/renderer/Ttf/Cache.lean#L90-L93
[`Ttf.Cache.put_payload_bound`]: engine/renderer/Ttf/Cache.lean#L112-L113
[`time_shown`]: ops/community/reaction/RowLaws.lean#L84-L87
[`tally_nodup`]: ops/community/reaction/RowLaws.lean#L56-L60
[`tally_mem`]: ops/community/reaction/RowLaws.lean#L68-L71
[`picBox_aspect`]: ops/community/reaction/RowLaws.lean#L19-L28
[`readable_held`]: ops/community/Intents.lean#L502-L514
[`readable_complete`]: ops/community/Intents.lean#L542-L552
[`switcherOrder_sound`]: ops/app/Pages.lean#L685-L687
[`switcherOrder_complete`]: ops/app/Pages.lean#L692-L694
[`dedupe_nodup`]: ops/app/Switch.lean#L52-L53
[`dedupe_one_per_community`]: ops/app/Switch.lean#L56-L58
[`select_tapped_dedupe`]: ops/app/Switch.lean#L82-L84
[`drawPage_key`]: App.lean#L918-L922
[`pageIn_acc`]: App.lean#L924-L927
[`msg_cmp`]: ops/community/message/Order.lean#L137-L144
[`time_is_display`]: ops/community/message/Order.lean#L148-L154
[`order_total`]: ops/community/message/Order.lean#L217-L227
[`Pos.cmp_eq_iff`]: engine/core/Order.lean#L44-L46
[`Pos.cmp_lt_trans`]: engine/core/Order.lean#L57-L59
[`send_after`]: ops/community/message/Order.lean#L424-L442
[`arrival_order`]: ops/community/message/Order.lean#L395-L407
[`receipt_once`]: ops/community/message/Order.lean#L352-L355
[`order_local`]: ops/community/message/Order.lean#L482-L494
[`display_agrees`]: ops/community/message/Order.lean#L524-L534
[`parse_segsBits`]: engine/renderer/qr/SegLaws.lean#L157-L161
[`parse_dataStream`]: engine/renderer/qr/SegLaws.lean#L193-L197
[`RS.correct_sound`]: engine/renderer/qr/Laws.lean#L55-L57
[`RS.correct_clean`]: engine/renderer/qr/Laws.lean#L74-L76
[`decodeFormat_correct`]: engine/renderer/qr/Format.lean#L104-L105
[`decodeVersion_correct`]: engine/renderer/qr/Format.lean#L113-L116
[`parse_text`]: ops/community/Link.lean#L198-L199
[`Base62.decode_encode`]: ops/community/Link.lean#L134-L134
[`Mdns.decode_encode`]: engine/wire/mdns/Laws.lean#L289-L290
[`decode_roundtrip`]: engine/wire/mdns/Laws.lean#L584-L587
[`render_wellFormed`]: engine/renderer/pic/Laws.lean#L219-L219
[`render_opaque`]: engine/renderer/pic/Laws.lean#L222-L226
[`scale_wellFormed`]: engine/renderer/pic/Laws.lean#L236-L236
[`fit_round`]: engine/renderer/pic/Laws.lean#L87-L90
[`Pic.layout_inside`]: engine/renderer/pic/Laws.lean#L170-L172
[`Pic.layout_apart`]: engine/renderer/pic/Laws.lean#L147-L148
[`write_offers`]: engine/wire/WorldLaws.lean#L502-L510
[`hold_wants`]: engine/wire/WorldLaws.lean#L520-L527
[`op_taken`]: engine/wire/WorldLaws.lean#L666-L673
[`write_offers_all`]: engine/wire/WorldLaws.lean#L1353-L1364
[`secrecy_runs`]: ops/sync/Witnesses.lean#L10-L14
[`reach_drain`]: engine/core/Proofs.lean#L529-L530
[`exchange_ids_stable`]: ops/sync/TreeLaws.lean#L163-L165
[`exchange_log`]: ops/sync/TreeLaws.lean#L210-L221
[`exchange_stable`]: ops/sync/TreeLaws.lean#L171-L179
[`reads_members`]: ops/connection/NodeLaws.lean#L78-L78
[`reads_recipients`]: ops/connection/NodeLaws.lean#L82-L82
[`admitted_inv`]: ops/connection/bootstrap/Scene.lean#L159-L162
[`allowedA`]: ops/connection/bootstrap/Scene.lean#L230-L230
[`allowedB`]: ops/connection/bootstrap/Scene.lean#L244-L247
[`allowPeer_iff`]: ops/connection/bootstrap/Bridge.lean#L29-L32
[`allowPeer_settles`]: ops/connection/bootstrap/Bridge.lean#L35-L39
[`fit_small`]: engine/renderer/pic/Laws.lean#L37-L37
[`fit_le`]: engine/renderer/pic/Laws.lean#L50-L50
[`fit_pos`]: engine/renderer/pic/Laws.lean#L59-L59
[`fit_long`]: engine/renderer/pic/Laws.lean#L71-L71
[`layout_sizes`]: engine/renderer/pic/Laws.lean#L143-L144
[`layout_apart`]: engine/renderer/pic/Laws.lean#L147-L148
[`add_stored`]: engine/renderer/pic/Laws.lean#L239-L242
[`decode_valid`]: engine/wire/mdns/Laws.lean#L540-L541
[`lit_zero`]: ops/community/attachment/ArrivalLaws.lean#L88-L89
[`lit_mono`]: ops/community/attachment/ArrivalLaws.lean#L92-L94
[`lit_full`]: ops/community/attachment/ArrivalLaws.lean#L98-L99
[`lit_clockwise`]: ops/community/attachment/ArrivalLaws.lean#L105-L110
[`ring_counts`]: ops/community/attachment/ArrivalLaws.lean#L279-L282
[`has_ofList`]: engine/core/WindowIndex.lean#L452-L453
[`ofList_wf`]: engine/core/WindowIndex.lean#L445-L445
[`screen_index`]: engine/renderer/Screen.lean#L258-L261
[`decoded_started`]: ops/app/Pics.lean#L241-L245
[`image_steady`]: ops/app/Pics.lean#L336-L339
[`image_settles`]: ops/app/Pics.lean#L398-L400
[`image_twice`]: ops/app/Pics.lean#L411-L415
[`RWorld.acts_shown`]: engine/renderer/ActsLaws.lean#L209-L218
[`seen_take`]: engine/renderer/BoardLaws.lean#L245-L246
[`World.inv_commit`]: engine/renderer/BoardLaws.lean#L335-L336
[`RWorld.inv_commit`]: engine/renderer/ReaderLaws.lean#L237-L238
[`RWorld.inv_pass`]: engine/renderer/ReaderLaws.lean#L410-L411
[`RWorld.inv_frame`]: engine/renderer/ReaderLaws.lean#L256-L256
[`inv_evict`]: engine/renderer/ReaderLaws.lean#L259-L260
[`RWorld.settle`]: engine/renderer/ReaderLaws.lean#L458-L460
[`World.inv_pass`]: engine/renderer/BoardLaws.lean#L373-L374
[`World.inv_frame`]: engine/renderer/BoardLaws.lean#L399-L399
[`World.settle`]: engine/renderer/BoardLaws.lean#L405-L410
[`marked_pass`]: engine/renderer/BoardLaws.lean#L448-L451
[`start_eq`]: engine/renderer/Heights.lean#L148-L149
[`find_spec`]: engine/renderer/Heights.lean#L173-L176
[`set_toList`]: engine/renderer/Heights.lean#L202-L206
[`push_ok`]: engine/renderer/Heights.lean#L328-L330
[`findM_cost`]: engine/renderer/Heights.lean#L571-L571
[`startM_cost`]: engine/renderer/Heights.lean#L589-L589
[`setM_cost`]: engine/renderer/Heights.lean#L607-L607
[`rows_cost`]: engine/renderer/Heights.lean#L627-L632
[`start_mono`]: engine/renderer/Heights.lean#L236-L237
[`start_size`]: engine/renderer/Heights.lean#L244-L245
[`below_window`]: engine/renderer/Heights.lean#L248-L251
[`above_window`]: engine/renderer/Heights.lean#L254-L258
[`plan_stmt_cost`]: engine/core/Query.lean#L600-L603
[`readPlan_cost`]: engine/core/Query.lean#L560-L565
[`readPlan_cost_le`]: engine/core/Query.lean#L611-L616
[`readPlan_cost_range`]: engine/core/Query.lean#L574-L577
[`walks_le`]: engine/core/Query.lean#L586-L586
[`fold_congr`]: ops/sync/TreeLaws.lean#L148-L151
[`deviceLive_lists`]: ops/app/PeopleLaws.lean#L145-L147
[`live_lists_ge`]: ops/app/PeopleLaws.lean#L180-L182
[`live_lists_le`]: ops/app/PeopleLaws.lean#L160-L164
[`presentW_lists`]: ops/app/PeopleLaws.lean#L221-L225
[`presentW_lists_eq`]: ops/app/PeopleLaws.lean#L204-L208
[`present_lists_eq`]: ops/app/PeopleLaws.lean#L214-L215
[`present_scans`]: ops/app/PeopleLaws.lean#L233-L236
[`unremoved_lists`]: ops/app/PeopleLaws.lean#L129-L130
[`matching_proj`]: engine/core/Project.lean#L366-L368
[`eval_proj`]: engine/core/Project.lean#L385-L389
[`filterMap_inlRow`]: engine/core/Project.lean#L404-L405
[`insertBy_map`]: engine/core/Project.lean#L350-L351
[`foldr_insertBy`]: engine/core/Union.lean#L105-L108
[`insertBy_merge`]: engine/core/Union.lean#L68-L71
[`mem_proj_idx`]: engine/core/Project.lean#L215-L216
[`sideCount_run`]: engine/core/Query.lean#L666-L669
[`splitWalk_cost`]: engine/core/Query.lean#L735-L740
[`splitWalk_exact`]: engine/core/Query.lean#L675-L678
[`splitWalk_steps`]: engine/core/Query.lean#L690-L696
[`perm_sortPos`]: engine/core/Decl.lean#L124-L125
[`sortPos_eq_fast`]: engine/core/Query.lean#L278-L279
[`sortPos_sorted`]: engine/core/Order.lean#L152-L153
[`sortPos_map`]: engine/core/Project.lean#L359-L360
[`mergeRuns_eq_sortPos`]: engine/core/Union.lean#L114-L117
[`union_rows`]: engine/core/Union.lean#L158-L164
[`specVerdict_eq_some`]: engine/core/Project.lean#L71-L72
[`AWorld.passActs_comp`]: engine/renderer/ActsLaws.lean#L291-L293
[`AWorld.passActs_indep`]: engine/renderer/ActsLaws.lean#L295-L298
[`AWorld.passActs_acts`]: engine/renderer/ActsLaws.lean#L301-L302
[`AWorld.type_only`]: engine/renderer/ActsLaws.lean#L304-L305
[`passActs_picks`]: engine/renderer/ActsLaws.lean#L98-L103
[`passActs_nil`]: engine/renderer/ActsLaws.lean#L141-L143
[`inv_passActs`]: engine/renderer/ActsLaws.lean#L192-L195
[`idxok_passActs`]: engine/renderer/ActsLaws.lean#L199-L203
[`withViewLast_moves`]: ops/app/Reader.lean#L94-L98
[`run_contiguous`]: engine/renderer/bidi/Laws.lean#L84-L87
[`erase_run`]: engine/core/CostErase.lean#L22-L23
[`erase_pure`]: engine/core/CostErase.lean#L25-L25
[`erase_bind`]: engine/core/CostErase.lean#L28-L29
[`erase_charged`]: engine/core/CostErase.lean#L38-L38
[`erase_chargedBy`]: engine/core/CostErase.lean#L41-L41
[`erase_lift`]: engine/core/CostErase.lean#L44-L44
[`erase_tick`]: engine/core/CostErase.lean#L47-L47
[`val_erase`]: engine/core/CostErase.lean#L55-L56
[`cost_run`]: engine/core/CostErase.lean#L58-L60
[`offerM`]: ops/app/NodeOffer.lean#L29-L35
[`Seal.Good`]: ops/community/Keys.lean#L40-L43
[`Symbolic.sym`]: ops/connection/NoiseSymbolic.lean#L259-L269
[`Model.run`]: engine/core/Model.lean#L103-L103
[`Sync.popW`]: engine/wire/LaneLaws.lean#L257-L260
[`Engine.runJ`]: engine/core/WindowLaws.lean#L148-L151
[`Engine.Inv`]: engine/core/Proofs.lean#L202-L219
<!-- /proof-links -->
