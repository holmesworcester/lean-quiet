# Lean Quiet

Quiet's engine, op families, apps and their proofs in Lean 4, in one
repository. Every part builds against the others at the same commit.

## What is proven

Lean checks these theorems about the code that runs. Whatever any peer
or anyone on the network does:

- **nobody can post as another member;** ¹
- **nobody joins without an invitation and members' approval;** ¹
- **only admins remove others, and no removal can be undone;** ¹
- **no peer can alter or rename an op:** its id is the hash of its
  bytes, and it has one parse; ²
- **non-members get none of a community's ops, and no device's secrets
  leave it;**
- **a node's trust rule lets in exactly the live members;** ¹
- **honest nodes that hold the same ops agree;** ²
- **only a session's two devices can derive its keys, even if both
  devices' long-term keys later leak.** ³

¹ assuming Ed25519 signatures cannot be forged. ² assuming SHA-256 has
no collisions. ³ in the symbolic model of the cryptography.

**Not yet proven:**
- that messages are secret from non-members (the seal's secrecy);
- that a removal reaches a live session from the removal itself, which
  needs `sum_project`;
- the bootstrap over the running code, rather than a model;
- that content is drawn faithfully all the way to pixels (proven up to
  each row's layout; painting is not).

### Assumed

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
  AEAD opens what it seals, and public keys are 32 bytes. With
  [`Keys.Good`], a device's Ed25519 key converts to its seed's X25519
  key. These are correctness only, and say nothing about secrecy.
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
  row against the model, and with kill -9 crash tests.
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
- **The seam:** the TCP runner's sockets, the C glue, and the Android and
  iOS shells. These are tested end to end, over localhost TCP and on
  devices.
- **That each statement says what we mean.** Read it: every name below
  links to its statement.

### How to read it

- **The attacker** is any peer, a removed member included, or anyone on
  the network. It sends any bytes, and replays, delays, reorders or
  drops any message. It cannot break the cryptography, or control a
  member's device.
- **Each theorem is about the functions that run** in the app and the
  daemon, over the engine's own store. *(model)* marks a theorem about
  a separate model instead.
- **The Community laws are proven over a store of that family alone.**
  The running node composes it with the Connection family. That
  composition is proven op by op (`sum_left`), but not yet for the
  whole store (`sum_project`, wanted below).
- **All 301 rest on Lean's standard axioms only:** no `sorry` and no
  added axiom, as `tests/check.sh` checks.
- **Each name links to its docstring and statement.**
  `ci/proof-links.py` writes the links from Lean's declaration ranges,
  and local CI fails when they go stale.

✅ proven · 🟡 partly · ⬜ wanted. 🥊🥊🥊 is what a user is promised;
🥊🥊 is what that rests on; 🥊 is supporting.

### Against an attacker

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
| ✅ | 🥊🥊🥊 | **Non-members get no ops, even by asking by id.** A session sends only sync messages, and ops of the rooms its peer is let into. | [`recv_send`] |
| ✅ | 🥊🥊🥊 | **Secrets stay on the device.** No local op (a secret, a session key, a pending join) is ever offered or sent. Of a connection's ops, only the two handshake messages are not local. | [`offer_shared`], [`wire_kinds`], [`local_kinds`], [`joinOps_travels`], [`found_travels`], [`stopWaiting_local`] |
| ✅ | 🥊🥊 | **The stream discloses only what it may.** It offers only ids of stored, shared ops, never one still pending. The clock sends only round messages and offers. | [`filed_send`], [`offer_stored`], [`tick_send`] |
| 🟡 | 🥊🥊🥊 | **Messages are sealed to members only.** Proven: a content key goes to exactly the live members' devices, and a member opens what was sealed under the key wrapped to it. A shared op's validator reads only shared facts. Wanted: that a non-member cannot open it (the seal's secrecy). | [`recipients_iff`], [`members_iff`], [`member_opens`], [`openSealed_seal`], [`unbox_box`], [`check_reads_shared`] |
| ✅ | 🥊🥊🥊 | **Sessions are secret and authenticated.** Suppose an attacker reads, replays and injects every message, and knows every key except the two devices' static keys and the session's ephemerals. Then neither transport key is derivable. The initiator accepts a reply only if it is exactly what the responder wrote answering this request. This is over the handshake functions that run, in the symbolic model (see Assumed). Replays are accepted again, and payloads are not covered. A negative control shows an attacker holding the initiator's keys does derive the session keys, and `kk_runs` shows the honest run exists. | [`kk_secret`], [`kk_secret_init`], [`kk_secret_resp`], [`kk_authentic`], [`kk_authentic_resp`], [`kk_secret_init_tight`], [`kk_runs`], [`handshake_agrees`] |
| 🟡 | 🥊🥊🥊 | **A closed session's keys cannot be recovered,** from the disk or from the static keys later. Proven: with the ephemerals gone, both static keys and the whole transcript do not give the session keys, and the session's rows are gone. Tested: no file of the database holds a byte of them (`tests/engine/Purge.lean`). Wanted: that closing purges every ephemeral (`close_forgets`). | [`kk_forward_secret`], [`kk_forward_secret_init`], [`kk_forward_secret_resp`], [`purge_gone`], [`purge_named`] |
| ⬜ | 🥊🥊🥊 | **Session secrets never reach the disk.** They would be ephemeral ops, held in memory, so forward secrecy would not rest on deletion. A restart then redials. | |
| ⬜ | 🥊🥊🥊 | **Removed members cannot read new messages.** This needs key rotation, which is not built. | |
| ⬜ | 🥊🥊 | **Every offered id names a stored op in one of the peer's rooms** (`have_shown`). This is the disclosure law for ids. | |
| | | **Connections** | |
| ✅ | 🥊🥊🥊 | **The trust rule lets in exactly the live members.** Read from the node's tables, it accepts exactly the devices of admitted, unremoved users. Nodes that hold the same ops agree on it. | [`connect_iff`], [`refuse_nonmember`], [`connect_approved`], [`connect_agree`] |
| ✅ | 🥊🥊🥊 | **A removal cuts the removed user out of the rule.** Once a node holds it, the rule refuses every device of that user, except a device also admitted into another live user. A device can be admitted under two users today. Whether that should hold is an open design question. Only an admin can remove another user, and nothing undoes it. | [`removal_cuts_off`], [`removals_iff`], [`removal_authorized`], [`removed_stays`] |
| 🟡 | 🥊🥊🥊 | **A removal ends a live session's sync.** Proven: a connection carries a room only if the trust rule takes its peer, and for a live member that rule is `allowPeer`. So a peer `allowPeer` refuses gets nothing of the room, and nothing of it is taken from them. Every connection step reads its rooms afresh. That is in the code and tested over TCP, with a negative control, but not a theorem. Wanted: deriving the refusal from the removal itself in the running node (`sum_project`). The session stays open, with no rooms. | [`rooms_trusted`], [`rooms_cut`], [`trusts_live`], [`rooms_model`], [`recv_send`], [`recv_take`], [`removal_cuts_off`] |
| ⬜ | 🥊🥊🥊 | **No packet goes to a removed member.** From the first run of the engine loop after a node decides a removal, it sends the removed user's devices nothing. No sealed frame (their sessions close), no handshake reply (a replayed request gets nothing), and no dial. A last notice of the removal itself might be allowed. Today their sessions stay open with no rooms, and a replayed request is answered with its old reply bytes. Both change first. | |
| 🟡 | 🥊🥊🥊 | **No session before approval,** however hellos are lost or replayed, and sessions form only with trusted peers. Proven over a model. Wanted over the running handshake (`answer_trusted`, `untrusted_silent`). | [`no_connection_before_approval`], [`sessions_trusted`] *(model)* |
| ✅ | 🥊🥊🥊 | **Peers cannot push ops in** outside the rooms they are let into, nor plant a device's local state. | [`recv_take`], [`intake_local`], [`stored_local`], [`local_fact_mine`], [`intakeConn_conn`] |
| ✅ | 🥊🥊 | **Both ends hold one session.** Two ends that complete a handshake hold the same hash, each names the other, and each one's send key is the other's receive key. A frame opens to what was sealed, for the connection it names. | [`established_agrees`], [`open_seal`], [`cid_seal`] |
| | | **Hostile input** | |
| ✅ | 🥊🥊🥊 | **One parse per op.** A decoded op re-encodes to exactly the bytes received, so there is no parser differential and no malleability: the signer, the hasher and every peer read the same op. Its id is the SHA-256 of those bytes, so a peer cannot name an op. A Valid op is exactly its body's encoding under its own type, so no re-typed copy of one is Valid. | [`Codec.encode_decode`], [`Op.id_decode`], [`distinct_of_collisionFree`], [`op_of_valid`] |
| ✅ | 🥊🥊🥊 | **Hostile bytes decode to a well-formed value or to nothing.** A QOI picture comes out at 1–2048 px a side, with exactly its pixels' bytes, so at most 16 MiB whatever it claims. An mDNS packet keeps its RFC limits, and its pointer chains end by construction. Invite links and QR segments are valid. | [`Pic.decode_sized`], [`Mdns.decode_valid`], [`Community.parse_valid`], [`Qr.parse_valid`] |
| ✅ | 🥊🥊🥊 | **Attachments authenticate themselves.** Any peer may relay a file's chunks, but a chunk is Valid only if it is its file's own slice. One op stands for each index, so download progress counts exactly the chunks held, and the chunks for every index put together are the file. This assumes SHA-256 has no second preimage on the tree's inputs, a premise shown satisfiable. No hash with 32-byte outputs is injective, so the laws assume nothing stronger. | [`chunk_is_slice`], [`verify_sound`], [`complete_assembles`], [`chunk_unique`], [`progress_exact`], [`assumptions_hold`], [`no_injective_hash`] |
| ✅ | 🥊🥊🥊 | **Judging cannot be hung.** From any state, judging empties its queue within a budget read off the tables. | [`drain_bounded`], [`drain_terminates`], [`step_budget`] |
| ⬜ | 🥊🥊🥊 | **Authenticate before parsing:** a sealed frame's payload is decoded only after its AEAD check passes. | |
| ⬜ | 🥊🥊 | **Bounded buffering:** a connection holds at most one maximal frame (1 MiB) and a read, whatever the peer's length fields say. | |
| ⬜ | 🥊🥊 | **No amplification:** a decoded op is no larger than its bytes, and decoding is linear in them. | |
| ⬜ | 🥊🥊 | **Resources are capped:** memory, rounds and frames per peer. | |

### Correctness

| | | Guarantee | Theorems |
|---|---|---|---|
| | | **The engine** | |
| ✅ | 🥊🥊🥊 | **Honest nodes agree.** The same ops, in any order, batching or interleaving, give the same verdicts. | [`same_ops_same_verdicts`], [`order_free`] |
| ✅ | 🥊🥊 | **Verdicts are the spec's, and final.** Once judging settles, every stored verdict is the spec's over the ops received, and no later op changes it. | [`drain_settles`], [`status_iff_spec`], [`spec_extends`], [`inv_ingest`], [`inv_step`] |
| ✅ | 🥊🥊🥊 | **Purge is safe.** A purged session or courier is gone, no shared op is ever deleted, and the engine settles on what remains. | [`purge_gone`], [`purge_shared`], [`purge_settles`] |
| ✅ | 🥊🥊 | **Purge takes exactly what it must.** It takes the named conn and local ops and their stored dependents. Shared dependents are judged again. | [`purge_named`], [`purge_undecides`], [`purge_inv`], [`mem_purgeSet`], [`reach_ops`] |
| ✅ | 🥊 | **Families compose, op by op:** adding a family changes no verdict or scope of the first's ops. Strict decoding round-trips. | [`sum_left`], [`sum_scope_left`], [`Codec.decode_encode`], [`Op.decode_bytes`] |
| ⬜ | 🥊🥊🥊 | **The Community laws hold in the running node** (`sum_project`). In the store composed with the Connection family, every Community view answers as it would in a store of the Community ops alone. This carries every law above to the node that runs. | |
| ✅ | 🥊🥊🥊 | **The honest path works.** A request with its invitation and both signatures is valid, an eligible member's approval is valid, and enough approvals admit and let the device in. The remover's intent writes only removals that stand. | [`request_valid`], [`approve_valid`], [`admit_admits`], [`connect_admitted`], [`removeMember_valid`] |
| | | **Sync** | |
| ✅ | 🥊🥊🥊 | **A sync round is complete.** Each side is sent exactly what the other holds in the range and it lacks. On any path, it takes at most one answer more than the two sides hold in the range. | [`exchange_complete`] |
| ✅ | 🥊🥊 | **Fingerprints are honest.** Equal Merkle labels mean equal sets, and a side opens a round with an honest claim. | [`lbl_inj`], [`opening_honest`], [`num_inj`] |
| ✅ | 🥊🥊🥊 | **Partial sync is safe.** A node that holds an op's requirement closure judges it as its peer does. | [`spec_local`] |
| 🟡 | 🥊🥊🥊 | **A joiner connects, and both sides converge,** over a socket that loses, duplicates and reorders. Proven over a model only. | [`bootstrap`], [`bootstrap_ideal`], [`bootstrap_possible`], [`reachable_inv`] *(model)* |
| ⬜ | 🥊🥊🥊 | **The running connection does all this.** It performs the round, and delivers each op's requirement closure (`conn_runs_exchange`, `closure_delivered`). This retires the bootstrap's model (`ops/connection/bootstrap/`). | |
| ⬜ | 🥊🥊🥊 | **New ops reach connected members.** An op stored while a member's connection is up is offered on it at once, if the member may see its room. The member holds it after one exchange (`stream_delivers`). Tested, not proven. | |
| ⬜ | 🥊🥊🥊 | **Everyone converges.** Under fair delivery, members linked by any chain of connections eventually hold every op of their community. By [`same_ops_same_verdicts`], they then hold the same verdicts. Proven so far for two nodes, over a model. | |
| ⬜ | 🥊🥊 | **Staleness is never hidden.** What the screen says about sync is true of the ops held. "Up to date as of T" means a round the device opened at its own time T ended with it holding everything the peer held in that room. If no round ends within a stated bound, the screen says so within that bound. | |
| ⬜ | 🥊🥊🥊 | **A synced page is complete:** after syncing a page, a device shows every row its peer shows for it (`page_sync`). | |
| ⬜ | 🥊🥊 | **Sync is efficient.** Each op is sent at most once per connection, and a round needs at most fan·Δ·⌈log n⌉ claims. | |
| ⬜ | 🥊 | **The cached Merkle tree's labels are `lbl`'s,** for O(log n) fingerprints with no change on the wire. | |
| | | **The screen** | |
| ✅ | 🥊🥊🥊 | **Nothing on screen is covered or mis-tapped.** Content in the viewport is drawn below the header, and above the composer and keyboard. Pinned to the bottom, the newest message is wholly visible. A tap lands on the row, or emoji key, drawn under it. | [`visible_in_viewport`], [`newest_visible`], [`pinned_visible`], [`pinned_tap`], [`hit_iff`] |
| ⬜ | 🥊🥊🥊 | **Every control is big enough to tap.** Every tappable control's hit area, not just its drawn size, is at least 48 dp by 48 dp on Android and 44 pt by 44 pt on iOS, at every supported screen size and text scale. | |
| ⬜ | 🥊🥊 | **A tap means one thing.** On every screen, no two controls' hit areas overlap, so a point selects at most one control. A tap selects the control drawn under it. Today this is proven for the emoji sheet and message rows only (`keys_disjoint`, `hit_iff`, `pinned_tap`). | |
| ⬜ | 🥊🥊 | **Every control shown can be tapped.** A control that is drawn has its hit area on screen, and not under the header, the composer or the keyboard. | |
| ⬜ | 🥊🥊 | **A tap acts once.** A second tap on a control while its action is in flight starts nothing new (Send sends once). A press that turns into a scroll past the slop is not a tap. | |
| ⬜ | 🥊🥊 | **Destructive actions are guarded.** Every action that cannot be undone asks for a second confirmation, as removal does (`writes_only_after_two`). Its control keeps a clear gap from the controls around it. | |
| ✅ | 🥊🥊🥊 | **A screen re-reads only what changed.** A list changes only when a row is filed under a key it read, and no list holds an op twice. | [`eval_stable`], [`view_stable`], [`filed_rel`], [`mem_keysOf`], [`matching_nodup`] |
| ✅ | 🥊🥊🥊 | **Removing someone takes two confirmations.** Nothing is written before the second, and cancelling writes nothing. Each attempt starts fresh, and one in flight cannot be replaced. The action is offered only to an admin, on another present member. | [`writes_only_after_two`], [`cancel_writes_nothing`], [`open_fresh`], [`no_replace`], [`offered_only`] |
| ✅ | 🥊🥊 | **The people list is the present members,** each once. A removed member leaves it and its count, but keeps their name on their messages. | [`present_iff`], [`present_nodup`] |
| ⬜ | 🥊🥊🥊 | **The screen is one moment.** Every frame is the root component drawn over a single settled store state, the latest the app has seen, so if one row is current, all are. Half of this is proven: a cached component whose keys did not fire answers as a fresh read would. Wanted: the renderer re-reads exactly what fired, and reads only between write turns. | [`eval_stable`], [`view_stable`], [`drain_bounded`] |
| ⬜ | 🥊🥊 | **An action's toast stays until the screen shows it.** A toast for an action (removing someone, a new name or avatar) stays up until every component on screen has re-read a state that holds the action's op, or until the OS's toast time passes, whichever comes first. So a toast that leaves early proves the screen has caught up. | |
| ✅ | 🥊🥊 | **The layout is exact.** The slide and keyboard shift are exact, and page rows are where the page put them. Emoji keys never overlap, and every key is reachable. An invite's hints and QR fit, and the camera preview reads inside its frame. | [`placed_row`], [`newest_drawn`], [`pinned_row`], [`keys_disjoint`], [`hit_cell`], [`reachable`], [`compose_row`], [`compose_top`], [`Link.hints_fit`], [`Link.qr_fits`], [`Camera.src_in`] |
| 🟡 | 🥊🥊🥊 | **Message text is shown faithfully.** A row's glyphs, read in order, are exactly the body's visible characters. Nothing is clipped, reordered or taken from another row, and every line fits. Proven: wrapping drops only spaces and keeps every other character in order, and every line fits when every character does; bidi reordering is a permutation (nothing dropped or invented); the glyphs placed are exactly the visible characters, each starting where the one before ends; numbers keep their order inside right-to-left text, for the reported cases. Wanted: that order in general, and `layout` as one statement over the three. | [`wrap_keeps`], [`wrap_fits`], [`visual_perm`], [`place_shows`], [`place_starts`], [`digits_keep_order`] |
| 🟡 | 🥊🥊🥊 | **Names are shown correctly.** A message row draws its author's name, as the views pick it, and no one else's. No bidi override or invisible character can disguise a name or a message. Proven: a row's name is its author's newest valid profile's (or "…"), and only a device admitted into that user can have written it; the row draws it cut to a logical prefix and an ellipsis, so a long name keeps its beginning in either direction. Every explicit bidi control (embeddings, overrides, isolates, LRM and RLM) is a neutral in the running bidi, so none can reorder a name or a message. A name hides nothing: every one of its characters is drawn, an invisible one as its own labelled glyph, so "Alice" and "Alice" with a zero-width space draw differently. Not covered: look-alike letters from other scripts (Latin a, Cyrillic а). | [`message_read`], [`profile_read`], [`profile_authorized`], [`no_renaming`], [`name_placed`], [`name_shows`], [`oneLine_prefix`], [`controls_neutral`] |
| ✅ | 🥊🥊 | **Times, reactions and pictures are shown as held:** the claimed time's clock, each reaction's count of distinct reactors, and each picture at its aspect inside its box. One pill per emoji, whose reactors are exactly who reacted with it, each once; a picture's box has one side at its bound and the other scaled by its aspect. | [`time_shown`], [`message_read`], [`tally_nodup`], [`tally_mem`], [`picBox_aspect`] |
| 🟡 | 🥊🥊🥊 | **What you see is what was sent.** The rows a device draws are the views of the facts its ops hold, from network to pixel. Proven, over a model where every list read is the engine's: a shown message is a valid fact of the store, and its row's name, time and text are its author's name, its claimed time and its body opened with a key the store holds; the conversation is exactly the messages under keys this device holds. Wanted: the same from the row's layout to its pixels. | [`message_read`], [`readable_held`], [`readable_complete`], [`eval_stable`] |
| ✅ | 🥊🥊🥊 | **Every community is reachable, and is one entry.** A switcher row's tap selects exactly the entry it draws, every entry has a row, no two entries share an acceptance or a community, and a page is drawn from its key alone, which names its entry's op, never a name. | [`switcherOrder_sound`], [`switcherOrder_complete`], [`dedupe_nodup`], [`dedupe_one_per_community`], [`select_tapped_dedupe`], [`drawPage_key`], [`pageIn_acc`] |
| ⬜ | 🥊🥊 | **The screen keeps up:** no blank rows past a latency bound, within a frame budget, with bounded reads. | |
| ✅ | 🥊🥊 | **Display order.** A channel sorts by a counter its devices share, then the claimed time (wall-clock minutes, for display), then the id: a strict total order. What a device sends sorts after everything it lists there, whatever its clock says. Past the counter cap (one member's claim saturates a channel), each device lists by its own receipts, in its own arrival order; devices with the same posts order any two alike unless both are saturated. | [`msg_cmp`], [`time_is_display`], [`order_total`], [`send_after`], [`arrival_order`], [`receipt_once`], [`order_local`], [`display_agrees`] |
| | | **Codes, pictures and discovery** | |
| ✅ | 🥊🥊 | **What the encoders write reads back.** This holds for QR segments and codewords, invite links and mDNS packets. QR error correction is sound, and format and version readings tolerate their designed bit errors. | [`parse_segsBits`], [`parse_dataStream`], [`RS.correct_sound`], [`RS.correct_clean`], [`decodeFormat_correct`], [`decodeVersion_correct`], [`parse_text`], [`Base62.decode_encode`], [`Mdns.decode_encode`], [`decode_roundtrip`] |
| ✅ | 🥊 | **Pictures render whole:** scaled and composited pictures are well-formed and opaque, and the tray's layout fits. | [`render_wellFormed`], [`render_opaque`], [`scale_wellFormed`], [`fit_round`], [`Pic.layout_inside`], [`Pic.layout_apart`] |

The theorems not listed here are lemmas. The axiom audit,
`tests/Axioms.lean`, lists them all.

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
[`Unforgeable`]: ops/community/Laws.lean#L270-L272
[`CollisionFree`]: engine/core/Proofs.lean#L542-L544
[`Distinct`]: engine/core/Proofs.lean#L538-L540
[`lbl_inj`]: ops/sync/Fp.lean#L264-L268
[`NoSecondPreimage`]: ops/community/Merkle.lean#L142-L143
[`assumptions_hold`]: ops/community/Merkle.lean#L539-L543
[`Suite.Good`]: ops/connection/Noise.lean#L61-L65
[`Keys.Good`]: ops/connection/Types.lean#L32-L36
[`no_impersonation`]: ops/community/Laws.lean#L289-L302
[`admission_needs_approval`]: ops/community/Laws.lean#L469-L477
[`admission_approved`]: ops/community/Laws.lean#L388-L398
[`request_invited`]: ops/community/Laws.lean#L352-L362
[`removal_authorized`]: ops/community/Laws.lean#L517-L520
[`admin_granted`]: ops/community/Laws.lean#L556-L557
[`removed_stays`]: ops/community/Laws.lean#L563-L566
[`valid_stays`]: ops/community/Laws.lean#L570-L574
[`message_authorized`]: ops/community/Laws.lean#L255-L261
[`approval_signed`]: ops/community/Laws.lean#L371-L381
[`invitation_issued`]: ops/community/Laws.lean#L337-L343
[`named_by_admin`]: ops/community/Laws.lean#L608-L610
[`admission_consented`]: ops/community/Laws.lean#L274-L280
[`admin_removal_stands`]: ops/community/Laws.lean#L528-L541
[`mutual_removal`]: ops/community/Laws.lean#L549-L553
[`removed_approver_admits`]: ops/community/Laws.lean#L488-L499
[`recv_send`]: ops/sync/ConnLaws.lean#L146-L148
[`offer_shared`]: engine/core/Sync.lean#L83-L86
[`wire_kinds`]: ops/connection/Laws.lean#L40-L41
[`local_kinds`]: ops/connection/Laws.lean#L47-L48
[`joinOps_travels`]: ops/community/Intents.lean#L299-L303
[`found_travels`]: ops/community/Intents.lean#L310-L314
[`stopWaiting_local`]: ops/community/Intents.lean#L306-L307
[`filed_send`]: ops/sync/ConnLaws.lean#L175-L178
[`offer_stored`]: engine/core/Sync.lean#L98-L101
[`tick_send`]: ops/sync/ConnLaws.lean#L184-L187
[`recipients_iff`]: ops/community/Connect.lean#L214-L218
[`members_iff`]: ops/community/Connect.lean#L205-L208
[`member_opens`]: ops/community/Laws.lean#L928-L932
[`openSealed_seal`]: ops/community/Laws.lean#L918-L920
[`unbox_box`]: ops/community/Keys.lean#L89-L91
[`check_reads_shared`]: ops/community/Laws.lean#L839-L841
[`kk_secret`]: ops/connection/NoiseSymbolic.lean#L595-L609
[`kk_secret_init`]: ops/connection/NoiseSymbolic.lean#L547-L556
[`kk_secret_resp`]: ops/connection/NoiseSymbolic.lean#L561-L569
[`kk_authentic`]: ops/connection/NoiseSymbolic.lean#L806-L820
[`kk_authentic_resp`]: ops/connection/NoiseSymbolic.lean#L872-L885
[`kk_secret_init_tight`]: ops/connection/NoiseSymbolic.lean#L616-L625
[`kk_runs`]: ops/connection/NoiseSymbolic.lean#L304-L312
[`handshake_agrees`]: ops/connection/Noise.lean#L308-L320
[`kk_forward_secret`]: ops/connection/NoiseSymbolic.lean#L685-L696
[`kk_forward_secret_init`]: ops/connection/NoiseSymbolic.lean#L643-L651
[`kk_forward_secret_resp`]: ops/connection/NoiseSymbolic.lean#L662-L671
[`purge_gone`]: engine/core/Purge.lean#L261-L263
[`purge_named`]: engine/core/Purge.lean#L267-L271
[`connect_iff`]: ops/community/Connect.lean#L146-L150
[`refuse_nonmember`]: ops/community/Connect.lean#L161-L164
[`connect_approved`]: ops/community/Connect.lean#L182-L193
[`connect_agree`]: ops/community/Connect.lean#L226-L229
[`removal_cuts_off`]: ops/community/Connect.lean#L241-L245
[`removals_iff`]: ops/community/Connect.lean#L43-L44
[`rooms_trusted`]: ops/connection/RoomLaws.lean#L74-L79
[`rooms_cut`]: ops/connection/RoomLaws.lean#L93-L103
[`trusts_live`]: ops/connection/RoomLaws.lean#L40-L46
[`rooms_model`]: ops/connection/RoomLaws.lean#L109-L111
[`recv_take`]: ops/sync/ConnLaws.lean#L118-L120
[`no_connection_before_approval`]: ops/connection/bootstrap/Laws.lean#L39-L46
[`sessions_trusted`]: ops/connection/bootstrap/Laws.lean#L63-L68
[`intake_local`]: engine/core/Sync.lean#L41-L43
[`stored_local`]: engine/core/Sync.lean#L137-L140
[`local_fact_mine`]: ops/community/Laws.lean#L627-L631
[`intakeConn_conn`]: engine/core/Sync.lean#L36-L37
[`established_agrees`]: ops/connection/Laws.lean#L51-L61
[`open_seal`]: ops/connection/Frame.lean#L51-L55
[`cid_seal`]: ops/connection/Frame.lean#L79-L82
[`Codec.encode_decode`]: engine/core/Codec.lean#L641-L644
[`Op.id_decode`]: engine/core/Core.lean#L89-L91
[`distinct_of_collisionFree`]: engine/core/Proofs.lean#L546-L549
[`op_of_valid`]: ops/community/Laws.lean#L227-L232
[`Pic.decode_sized`]: engine/renderer/pic/Laws.lean#L198-L201
[`Mdns.decode_valid`]: engine/wire/mdns/Laws.lean#L540-L541
[`Community.parse_valid`]: ops/community/Link.lean#L213-L214
[`Qr.parse_valid`]: engine/renderer/qr/SegLaws.lean#L336-L338
[`chunk_is_slice`]: ops/community/Laws.lean#L673-L682
[`verify_sound`]: ops/community/Merkle.lean#L431-L437
[`complete_assembles`]: ops/community/Merkle.lean#L478-L484
[`chunk_unique`]: ops/community/Laws.lean#L763-L769
[`progress_exact`]: ops/community/Intents.lean#L618-L627
[`no_injective_hash`]: ops/community/Merkle.lean#L241-L243
[`drain_bounded`]: engine/core/Budget.lean#L163-L168
[`drain_terminates`]: engine/core/Termination.lean#L84-L87
[`step_budget`]: engine/core/Budget.lean#L124-L126
[`same_ops_same_verdicts`]: engine/core/Termination.lean#L118-L126
[`order_free`]: engine/core/Proofs.lean#L634-L639
[`drain_settles`]: engine/core/Termination.lean#L110-L114
[`status_iff_spec`]: engine/core/Proofs.lean#L483-L485
[`spec_extends`]: engine/core/SpecLemmas.lean#L137-L139
[`inv_ingest`]: engine/core/Proofs.lean#L229-L229
[`inv_step`]: engine/core/Proofs.lean#L260-L260
[`purge_shared`]: engine/core/Purge.lean#L274-L276
[`purge_settles`]: engine/core/Budget.lean#L192-L198
[`purge_undecides`]: engine/core/Proofs.lean#L376-L383
[`purge_inv`]: engine/core/Proofs.lean#L391-L395
[`mem_purgeSet`]: engine/core/Proofs.lean#L364-L368
[`reach_ops`]: engine/core/Proofs.lean#L624-L626
[`sum_left`]: engine/core/Families.lean#L79-L82
[`sum_scope_left`]: engine/core/Families.lean#L85-L86
[`Codec.decode_encode`]: engine/core/Codec.lean#L635-L635
[`Op.decode_bytes`]: engine/core/Core.lean#L94-L94
[`request_valid`]: ops/community/Laws.lean#L409-L417
[`approve_valid`]: ops/community/Laws.lean#L425-L433
[`admit_admits`]: ops/community/Laws.lean#L441-L452
[`connect_admitted`]: ops/community/Connect.lean#L169-L179
[`removeMember_valid`]: ops/community/Intents.lean#L484-L491
[`exchange_complete`]: ops/sync/RoundLaws.lean#L232-L241
[`opening_honest`]: ops/sync/RoundLaws.lean#L323-L325
[`num_inj`]: ops/sync/Fp.lean#L37-L37
[`spec_local`]: engine/core/Locality.lean#L54-L58
[`bootstrap`]: ops/connection/bootstrap/Laws.lean#L401-L405
[`bootstrap_ideal`]: ops/connection/bootstrap/Laws.lean#L423-L424
[`bootstrap_possible`]: ops/connection/bootstrap/Laws.lean#L208-L218
[`reachable_inv`]: ops/connection/bootstrap/Steps.lean#L222-L223
[`visible_in_viewport`]: engine/renderer/Geometry.lean#L90-L95
[`newest_visible`]: engine/renderer/Geometry.lean#L99-L105
[`pinned_visible`]: engine/renderer/Geometry.lean#L147-L151
[`pinned_tap`]: engine/renderer/Geometry.lean#L154-L157
[`hit_iff`]: engine/renderer/SheetGeom.lean#L93-L95
[`eval_stable`]: engine/core/View.lean#L137-L142
[`view_stable`]: engine/core/View.lean#L163-L165
[`filed_rel`]: engine/core/Decl.lean#L189-L196
[`mem_keysOf`]: engine/core/Decl.lean#L79-L82
[`matching_nodup`]: engine/core/Decl.lean#L158-L161
[`writes_only_after_two`]: ops/app/Remove.lean#L56-L59
[`cancel_writes_nothing`]: ops/app/Remove.lean#L63-L64
[`open_fresh`]: ops/app/Remove.lean#L67-L69
[`no_replace`]: ops/app/Remove.lean#L74-L76
[`offered_only`]: ops/app/Remove.lean#L83-L86
[`present_iff`]: ops/app/PeopleLaws.lean#L27-L30
[`present_nodup`]: ops/app/PeopleLaws.lean#L37-L38
[`placed_row`]: engine/renderer/Geometry.lean#L81-L85
[`newest_drawn`]: engine/renderer/Geometry.lean#L108-L111
[`pinned_row`]: engine/renderer/Geometry.lean#L141-L144
[`keys_disjoint`]: engine/renderer/SheetGeom.lean#L148-L150
[`hit_cell`]: engine/renderer/SheetGeom.lean#L144-L146
[`reachable`]: engine/renderer/SheetGeom.lean#L165-L168
[`compose_row`]: engine/renderer/SheetGeom.lean#L189-L193
[`compose_top`]: engine/renderer/SheetGeom.lean#L199-L202
[`Link.hints_fit`]: ops/community/link/View.lean#L49-L51
[`Link.qr_fits`]: ops/community/link/View.lean#L67-L67
[`Camera.src_in`]: engine/renderer/Camera.lean#L51-L53
[`wrap_keeps`]: engine/renderer/WrapLaws.lean#L132-L135
[`wrap_fits`]: engine/renderer/WrapLaws.lean#L206-L209
[`visual_perm`]: engine/renderer/TextLaws.lean#L46-L47
[`place_shows`]: engine/renderer/TextLaws.lean#L72-L74
[`place_starts`]: engine/renderer/TextLaws.lean#L138-L144
[`digits_keep_order`]: engine/renderer/TextLaws.lean#L119-L126
[`message_read`]: ops/community/message/ViewLaws.lean#L61-L66
[`profile_read`]: ops/community/message/ViewLaws.lean#L39-L41
[`profile_authorized`]: ops/community/Laws.lean#L307-L314
[`no_renaming`]: ops/community/Laws.lean#L321-L332
[`name_placed`]: ops/community/reaction/RowLaws.lean#L89-L93
[`name_shows`]: engine/renderer/TextLaws.lean#L158-L163
[`oneLine_prefix`]: engine/renderer/TextLaws.lean#L107-L108
[`controls_neutral`]: engine/renderer/TextLaws.lean#L182-L186
[`time_shown`]: ops/community/reaction/RowLaws.lean#L84-L87
[`tally_nodup`]: ops/community/reaction/RowLaws.lean#L56-L60
[`tally_mem`]: ops/community/reaction/RowLaws.lean#L68-L71
[`picBox_aspect`]: ops/community/reaction/RowLaws.lean#L19-L28
[`readable_held`]: ops/community/Intents.lean#L407-L419
[`readable_complete`]: ops/community/Intents.lean#L447-L457
[`switcherOrder_sound`]: ops/app/Pages.lean#L657-L659
[`switcherOrder_complete`]: ops/app/Pages.lean#L664-L666
[`dedupe_nodup`]: ops/app/Switch.lean#L52-L53
[`dedupe_one_per_community`]: ops/app/Switch.lean#L56-L58
[`select_tapped_dedupe`]: ops/app/Switch.lean#L82-L84
[`drawPage_key`]: App.lean#L929-L933
[`pageIn_acc`]: App.lean#L935-L938
[`msg_cmp`]: ops/community/message/Order.lean#L137-L144
[`time_is_display`]: ops/community/message/Order.lean#L148-L154
[`order_total`]: ops/community/message/Order.lean#L168-L175
[`send_after`]: ops/community/message/Order.lean#L365-L383
[`arrival_order`]: ops/community/message/Order.lean#L336-L348
[`receipt_once`]: ops/community/message/Order.lean#L293-L296
[`order_local`]: ops/community/message/Order.lean#L423-L435
[`display_agrees`]: ops/community/message/Order.lean#L465-L475
[`parse_segsBits`]: engine/renderer/qr/SegLaws.lean#L157-L161
[`parse_dataStream`]: engine/renderer/qr/SegLaws.lean#L193-L197
[`RS.correct_sound`]: engine/renderer/qr/Laws.lean#L55-L57
[`RS.correct_clean`]: engine/renderer/qr/Laws.lean#L74-L76
[`decodeFormat_correct`]: engine/renderer/qr/Format.lean#L104-L105
[`decodeVersion_correct`]: engine/renderer/qr/Format.lean#L113-L116
[`parse_text`]: ops/community/Link.lean#L197-L198
[`Base62.decode_encode`]: ops/community/Link.lean#L133-L133
[`Mdns.decode_encode`]: engine/wire/mdns/Laws.lean#L289-L290
[`decode_roundtrip`]: engine/wire/mdns/Laws.lean#L584-L587
[`render_wellFormed`]: engine/renderer/pic/Laws.lean#L219-L219
[`render_opaque`]: engine/renderer/pic/Laws.lean#L222-L226
[`scale_wellFormed`]: engine/renderer/pic/Laws.lean#L236-L236
[`fit_round`]: engine/renderer/pic/Laws.lean#L87-L90
[`Pic.layout_inside`]: engine/renderer/pic/Laws.lean#L170-L172
[`Pic.layout_apart`]: engine/renderer/pic/Laws.lean#L147-L148
<!-- /proof-links -->
