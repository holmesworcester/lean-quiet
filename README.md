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
- [**The seam**](#the-seam): the native code that connects Lean to the
  OS, and the libraries it calls. It is tested end to end, over
  localhost TCP and on devices.
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
- **All 275 rest on Lean's standard axioms only:** no `sorry` and no
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
| 🟡 | 🥊🥊🥊 | **Peers cannot push ops in** outside the rooms they are let into, nor plant a device's local state. Proven for sessions. **Not yet for the handshake:** a bare request's hello payload has its shared ops stored before the trust check. So a removed member, or an outsider who knows the community, can push ops in with no session. A fix is in progress. | [`recv_take`], [`intake_local`], [`stored_local`], [`local_fact_mine`], [`intakeConn_conn`] |
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
| 🟡 | 🥊🥊🥊 | **Names are shown correctly.** A message row draws its author's name, as the views pick it, and no one else's. No bidi override or invisible character can disguise a name or a message. Proven: a row's name is its author's newest valid profile's (or "…"), and only a device admitted into that user can have written it; the row draws it cut to a logical prefix and an ellipsis, so a long name keeps its beginning in either direction. Every explicit bidi control (embeddings, overrides, isolates, LRM and RLM) is a neutral in the running bidi, so none can reorder a name or a message, and the marks draw nothing. | [`message_read`], [`profile_read`], [`profile_authorized`], [`no_renaming`], [`name_placed`], [`oneLine_prefix`], [`controls_neutral`], [`marks_invisible`] |
| ✅ | 🥊🥊 | **Times, reactions and pictures are shown as held:** the claimed time's clock, each reaction's count of distinct reactors, and each picture at its aspect inside its box. One pill per emoji, whose reactors are exactly who reacted with it, each once; a picture's box has one side at its bound and the other scaled by its aspect. | [`time_shown`], [`message_read`], [`tally_nodup`], [`tally_mem`], [`picBox_aspect`] |
| 🟡 | 🥊🥊🥊 | **What you see is what was sent.** The rows a device draws are the views of the facts its ops hold, from network to pixel. Proven, over a model where every list read is the engine's: a shown message is a valid fact of the store, and its row's name, time and text are its author's name, its claimed time and its body opened with a key the store holds; the conversation is exactly the messages under keys this device holds. Wanted: the same from the row's layout to its pixels. | [`message_read`], [`readable_held`], [`readable_complete`], [`eval_stable`] |
| ✅ | 🥊🥊🥊 | **Every community is reachable, and is one entry.** A switcher row's tap selects exactly the entry it draws, every entry has a row, no two entries share an acceptance or a community, and a page is drawn from its key alone, which names its entry's op, never a name. | [`switcherOrder_sound`], [`switcherOrder_complete`], [`dedupe_nodup`], [`dedupe_one_per_community`], [`select_tapped_dedupe`], [`drawPage_key`], [`pageIn_acc`] |
| ⬜ | 🥊🥊 | **The screen keeps up:** no blank rows past a latency bound, within a frame budget, with bounded reads. | |
| ⬜ | 🥊🥊 | **Display order** (design in `docs/SYNC.md`). Devices with the same ops order messages alike, except a saturated tail, which follows receipt order. | |
| | | **Codes, pictures and discovery** | |
| ✅ | 🥊🥊 | **What the encoders write reads back.** This holds for QR segments and codewords, invite links and mDNS packets. QR error correction is sound, and format and version readings tolerate their designed bit errors. | [`parse_segsBits`], [`parse_dataStream`], [`RS.correct_sound`], [`RS.correct_clean`], [`decodeFormat_correct`], [`decodeVersion_correct`], [`parse_text`], [`Base62.decode_encode`], [`Mdns.decode_encode`], [`decode_roundtrip`] |
| ✅ | 🥊 | **Pictures render whole:** scaled and composited pictures are well-formed and opaque, and the tray's layout fits. | [`render_wellFormed`], [`render_opaque`], [`scale_wellFormed`], [`fit_round`], [`Pic.layout_inside`], [`Pic.layout_apart`] |

The theorems not listed here are lemmas. The axiom audit,
`tests/Axioms.lean`, lists them all.

## The seam

**Lean does the work; native code connects it to the OS.** Lean runs
the engine, the protocol and the UI, and paints every pixel the app
shows. Native code gives Lean what only the OS has: the window and the
compositor, touches, the keyboard, scrolling's physics, the camera and
the clipboard. It also calls the libraries that store the bytes and do
the crypto.

**Some native code does more than connect.** It decides what a touch
is, places the list, bounds the scroll offset, applies its own rules to
crypto inputs, assumes the iOS camera's orientation, and starts a
control channel at every launch. Two of its pixel steps are work Lean
could do. All of this is listed under
[More than interfacing](#more-than-interfacing), and it moves first in
the checklist.

| runs on | Lean in the app | our native code | under it |
|---|---|---|---|
| **Android** | 18,376 lines: the engine 10,434, the app 5,657, `engine/renderer/qr/`'s Qr 2,285 | 2,920 lines of C, Java and Rust | SQLite 3.50.4, the Rust crypto crates, and Lean's runtime and libuv 1.51.0 built from source |
| **iOS** | the same | 1,580 lines of C, Objective-C and Rust | the same |
| **the desktop and tests** | the same, and 4,861 lines of tests | 671 lines of C and Rust | the system's SQLite, the same crates, the toolchain's own runtime |

- Counts are non-blank lines, comments included, and the Lean counts
  include the proofs. With each native file counted once, there are
  4,527 lines in all. `engine/wire/mdns/` (949) and `ops/connection/bootstrap/` (1,385)
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

**What Lean does:** the engine and judging, the store's logic, sync,
the TCP runner's framing, the handshake and sessions, the trust rule,
every screen's layout and paint, QR decoding from the camera's raw
luma, and what each control command means. **None of the native code
is proven:** the proofs take it, and the libraries under it, as given.
The rest of this section is the native side.

### Platform-only

What Lean cannot reach without the OS.

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **The Android activity** ([`activity.c`](platforms/android/twin/activity.c), [`activity.h`](platforms/android/twin/activity.h)) | 662 | The NativeActivity's callbacks: the surface, touches, insets and the Java half's events, under one lock. It runs Lean's main on a thread of its own (256 MB of stack), sends stdout to logcat, and copies the APK's assets to the data directory. | Touches and insets arrive as the OS gave them, in order. |
| **The Java half** ([`LeanActivity.java`](platforms/android/twin/java/com/holmes/leanquiet/LeanActivity.java)) | 312 | The insets at every frame of the keyboard's animation. A hidden EditText holds the composer's text, so every input method works. Send, the clipboard, and the back camera's luma (Camera2). | The text, selection and composition Lean reads are the EditText's. |
| **The compositor** ([`layer.c`](platforms/android/twin/layer.c), [`layer.h`](platforms/android/twin/layer.h)) | 566 | A vsync thread (AChoreographer) shows Lean's three frames as three ASurfaceControl layers, in one transaction per vsync: the list slid for the offset and lifted by the keyboard, the header, and the composer riding the keyboard. Each layer has three buffers, each reused only once the compositor releases it. | The list lands where `Seam.place` says (see More than interfacing). |
| **Scrolling** ([`scroll.c`](platforms/android/twin/scroll.c), [`scroll.h`](platforms/android/twin/scroll.h)) | 308 | Android's own VelocityTracker and OverScroller through JNI, with the device's ViewConfiguration, so a fling feels like any Android list. | Nothing: the offset is an input to every theorem. |
| **UIKit** ([`quiet_ios.m`](platforms/ios/quiet_ios.m)) | 978 | All of the above on iOS: an upside-down UIScrollView, whose offset is the bottom-anchored one; IOSurface layer contents changed in one Core Animation transaction; a clear UITextField; UIKit's tap and long-press recognizers; the keyboard layout guide; AVFoundation's camera; the pasteboard; the display link. It also implements the externs, as quiet_android.c does on Android. | A layer in the flipped scroll view lands at `shown`, and a tap reports `tapped`. [`Placement.lean`](platforms/ios/Placement.lean) proves the rest from Geometry. |
| **The control channel** ([`ctl.c`](platforms/android/twin/ctl.c), [`ctl_ios.c`](platforms/ios/ctl_ios.c)) | 416 | The line protocol tests drive the app through: the abstract unix socket `@leanquiet` on Android, TCP on 127.0.0.1:7417 on iOS. Lean's `App.command` gives each line its meaning. | Nothing. It starts at every launch (see More than interfacing). |
| **Heap tags off** ([`notag.c`](platforms/android/leanrt/notag.c)) | 10 | Lean's runtime drops a pointer's top byte, which arm64 Android tags, so tagging is turned off before anything allocates. | Nothing. |
| **The headless twin** ([`host.c`](platforms/headless/host.c)) | 315 | Platform.lean's externs with no OS, driven by a script, with PPM dumps of the screen. | Nothing: it runs in tests only. |

### Pixels

**Painting is Lean's.** Glyphs are blitted from a prebuilt bitmap of GNU
Unifont ([`Font.lean`](engine/renderer/Font.lean),
[`Paint.lean`](engine/renderer/Paint.lean)). Pictures are decoded (QOI) and
box-filtered in Lean, and rows are painted on Lean's task threads. No
font is rasterized at run time: [`font.py`](tools/font.py) scales
Unifont up (Scale3x) and [`emoji.py`](tools/emoji.py) resamples
Noto Color Emoji into QOI pictures, at build time. emoji.py also
decides which code points draw as emoji (Unicode's presentation rules),
as a flag Lean reads.

Native code copies the finished rows into the OS's buffers:

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **Into the OS's buffers** (`bl_present` in [`layer.c`](platforms/android/twin/layer.c), `lq_fill_surface` in quiet_ios.m) | 77, 34 | memcpy into an AHardwareBuffer or an IOSurface, waiting a bounded time for one the compositor is not reading. | Nothing. |
| **The window's background** (`lq_paint` in [`quiet_android.c`](platforms/android/twin/quiet_android.c)) | 19 | Fills a new window with the list's background colour, which shows where a slide uncovers rows. | Nothing. |

Two more steps on the way, row reuse and iOS's byte order, are work
Lean could do. They are under More than interfacing.

### Libraries

| | what it gives | what the proofs assume of it |
|---|---|---|
| **The Rust crypto** ([`lib.rs`](engine/native/crypto/src/lib.rs), 145 lines, over ed25519-dalek 3.0.0, curve25519-dalek 5.0.0, chacha20poly1305 0.11.0, sha2 0.10.9 and getrandom 0.3.4) | SHA-256; Ed25519, verified strictly; X25519; the Ed25519 to X25519 conversion; ChaCha20-Poly1305 with Noise's nonce; XChaCha20-Poly1305; the OS's random bytes. One build on every platform. | [`Unforgeable`], [`CollisionFree`], [`NoSecondPreimage`], [`Suite.Good`] and [`Keys.Good`] (see Assumed). Tested byte for byte against libsodium ([`crypto_compat.c`](tests/engine/crypto_compat.c)) and against the Noise test vectors. |
| **SQLite** | The store. Phones ship the vendored 3.50.4 ([`third_party/sqlite`](third_party/sqlite)). The desktop links the system's `libsqlite3`, 3.46.1 on the machine local CI runs on. | It behaves like the engine's model ([`Model.lean`](engine/core/Model.lean)). This is tested row for row, with kill -9 crashes and the purge's raw read, on the desktop's SQLite only. |
| **Lean's runtime and libuv** | Reference counting; the ByteArray, String and Array primitives, which are `@[extern]` in Lean's core and implemented in C; tasks and threads; files; clocks; and Std.Async, which gives the TCP runner its sockets ([`Tcp.lean`](engine/wire/Tcp.lean)), mDNS its UDP, and an invite its dial hints (the interface addresses). Phones build it from Lean's source ([`build.sh`](platforms/android/leanrt/build.sh), [`leanrt.sh`](platforms/ios/leanrt.sh)), with no mimalloc and no GMP, OpenSSL stubbed, and libuv compiled from its source lists. | **Lean** in Trusted. The proofs reason about the core's Lean definitions, and the C must match them. The phones' build is not the one the tests run on. |

### FFI glue

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **Platform.lean on Android** ([`quiet_android.c`](platforms/android/twin/quiet_android.c)) | 528 | The 14 externs. Each frame's three row arrays go into the layers. Touches and the Java half's events come back as four words each, the layout `App.Event.decode` reads. The text, the camera's luma (into a ByteArray) and the clipboard. A watchdog logs a backtrace of Lean's thread if it stalls 3 s. | The words mean what `Event.decode` reads. |
| **SQLite** ([`glue.c`](engine/native/glue.c), [`glue_android.c`](platforms/android/native/glue_android.c)) | 72, 76 | Open, exec, and one statement with blob parameters, every column back as bytes. glue_android.c's SQLite code is a copy of glue.c's, over the vendored SQLite; iOS links it too. | Rows come back as stored. |
| **The crypto** ([`crypto.c`](engine/native/crypto.c)) | 139 | Checks sizes, calls the Rust, and wipes secret bytes from its stack. | Its size rules do more than interface (below). |
| **Text** (`ba_utf8` in activity.c, `cp` in LeanActivity.java, `lq_cp` in quiet_ios.m) | 37, 4, 11 | UTF-16 to UTF-8, and the selection and composition in code points, three ways. | The positions index the text Lean gets. |

Lean's side of the seam is every `@[extern]`, each an `opaque` Lean
cannot see into:

| Lean | C | what |
|---|---|---|
| `Engine.sha256` ([`Core.lean`](engine/core/Core.lean)) | `le_sha256` in crypto.c | SHA-256 |
| `Community.edKeypair`, `edSign`, `edVerify` ([`Compose.lean`](ops/community/Compose.lean)) | `le_ed25519_*` in crypto.c | Ed25519 |
| `Engine.Crypto.x25519`, `x25519Base`, `staticOf`, `staticPubOf`, `chachaSeal`, `chachaOpen`, `xchachaSeal`, `xchachaOpen`, `randomBytes` ([`Crypto.lean`](engine/core/Crypto.lean)) | `le_*` in crypto.c | X25519, the key conversion, the two AEADs, random bytes |
| `Engine.Db.open`, `exec` and `query`, over the opaque type `DbPointed` ([`Sqlite.lean`](engine/core/Sqlite.lean)) | `le_sql_*` in glue.c and glue_android.c | SQLite |
| The 14 of [`Platform.lean`](engine/renderer/Platform.lean): `screen`, `scroll`, `scrollBy`, `scrollTo`, `frame`, `text`, `ime`, `textClear`, `copy`, `ctlPoll`, `ctlReply`, `scan`, `luma`, `nowUs` | `lq_*` in each twin | the platform |
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

### More than interfacing

This native code does more than connect Lean to the OS: it makes
decisions, or does work Lean could do. The proofs do not cover it, and
it moves first in the checklist below.

**Decisions made in native code:**

| | lines | the decision | the proofs |
|---|---|---|---|
| **What a touch is** (`lq_pump` and `lq_release_at` in quiet_android.c, `tap` in host.c) | 68, 19, 10 | A press that stays within 8 dp is a tap, or a long press at 500 ms. A finger that goes down on the composer is also reported as a drag, the app's to scroll. The region is where the finger went down. A list tap's screen row y becomes the content distance `b + composerTop - 1 - y`, at the latest vsync's offset b (on a page, plus the keyboard's shift). | [`hit_iff`] and [`pinned_tap`] take that distance as given; `tapRow` states the formula the C must apply. On iOS UIKit decides, and Placement.lean proves the conversion from UIKit's layout. |
| **Where the list lands** (`bl_place_list`, and the composer's top in `bl_vsync`, in layer.c; `dump` in host.c) | 14, 34 | Frame row r, drawn at offset bf, goes to screen row `top - over - shift + (bn - bf) + r` for the vsync's offset bn (a page: `top - over + r`), cropped to the viewport. The composer's top is `h - bot - max(ime, inset)`. | [`placed_row`], [`visible_in_viewport`] and [`newest_visible`] are about `Seam.place`. That the C computes the same is trusted, as Geometry.lean says. |
| **The offset** (`bs_touch`, `bs_at`, `bs_pending` and `bs_vsync` in scroll.c; `bl_ahead` in layer.c) | 116, 27 | A drag follows the finger, resampled 5 ms before the vsync. The offset stays within 0 and the content's height less the viewport's. During a fling, Lean draws at the offset predicted for when its frame shows: at most two vsyncs ahead, and short of where the fling stops. | Nothing. |
| **Which input counts** (`ba_push` and `ba_motion` in activity.c; the editor action in LeanActivity.java; `textFieldShouldReturn` in quiet_ios.m) | 15, 29 | Only the first finger counts. A full queue drops moves but keeps downs and ups. The keyboard's Send, or Enter, sends. | Nothing. |
| **Crypto sizes** (crypto.c) | | A ChaCha20-Poly1305 key that is not 32 bytes seals under 32 zero bytes, while opening refuses it. XChaCha20-Poly1305 with a wrong-sized key or nonce seals to empty bytes. A wrong-sized Ed25519 seed gives empty bytes. | [`Suite.Good`] and `Seal.Good` say the AEAD opens what it seals for every key and nonce. The running AEADs do so only for 32-byte keys and 24-byte nonces. |
| **The camera on iOS** (quiet_ios.m) | | The back camera at 1280 × 720, oriented 90° always. Android reads the sensor's own orientation. | [`Camera.src_in`] takes the frame's header as given. |
| **The control channel** (ctl.c and ctl_ios.c, started by activity.c and quiet_ios.m) | | It starts at every launch, with no authentication. On Android it is the abstract socket `@leanquiet`. On iOS it is 127.0.0.1:7417 unless `LEANQUIET_CTL_PORT=0`, and every interface with `LEANQUIET_CTL_ADDR=any`. Its commands include `send` (posts as this device), `invite` (the current invite link), `found` and `chaos` (both write ops), and `state` (the composer's text). An abstract socket has no file permissions; what Android's SELinux policy lets other apps reach was not checked. | Nothing. The attacker is the network's; another process on the device is not in the model. |

- **No protocol decision is native.** The handshake, framing, sync
  rounds, the trust rule and judging are Lean, and the TCP and UDP under
  them are Lean's own Std.Async.
- **The placement formula has four copies:** Geometry.lean's (proven),
  layer.c's (Android), host.c's (the headless twin) and
  `platforms/headless/Sim.lean`'s (the host tests, without the slide or the
  keyboard). iOS gets it from UIKit's layout.

**Performance work Lean could do:**

| | lines | what it does | what the proofs assume of it |
|---|---|---|---|
| **Row reuse** (`lq_stage` in quiet_android.c and in quiet_ios.m) | 57, 63 | Copies a frame into a staging buffer. It skips each row that is the same Lean object as the last frame's, at the place the offset's change moves it to. The last frame is held, so a row seen again is the same immutable row. Lean knows which rows it painted, so it could say which are new. | A skipped row holds the same pixels. |
| **Byte order on iOS** (`lq_row` in quiet_ios.m) | 12 | Swizzles every pixel from R G B X to B G R A. Android's buffers take R G B X as it is, so there Lean's rows are copied unchanged. | Nothing. |

No Lean version of these exists, and none was timed for this README. The
Android twin logs its own costs every 120 frames: Lean's time per
frame, the copy's time and rows copied, and the time handing frames over
(`lq_time`); and missed vsyncs and rows left uncovered (`bl_stats` in
layer.c). The app's host session (`mise run host:app`) reports Lean's
step time and unpainted rows on a fling. The checklist below measures
with these.

### How it is tested

- **On devices, by hand:** `android:twin-demo-e2e`, `android:scan-e2e`,
  `ios:sim-e2e` and `ios:e2e` (mise.toml). `ci/workflow.yml` would
  run the first and the third on self-hosted runners; it is not in use.
- **Local CI runs no native twin.** It drives the app through
  `platforms/headless/Sim.lean`'s `Io`. host.c runs only in `mise run
  host:twin-demo`.
- **The engine's tests run the crypto and SQLite glue:** against
  libsodium, against the model, through kill -9, the purge's raw read,
  and two nodes over localhost TCP.

### Moving work into Lean

Most valuable first. The first eight are the native code that does
more than interface; the last is glue.

- [ ] **Decide taps and keys in Lean.**
  - Moves: `lq_pump` and `lq_release_at` (87 lines of quiet_android.c),
    host.c's `tap`, the first-finger rule in `ba_motion`, and "Enter
    sends" in LeanActivity.java and quiet_ios.m.
  - Instead: the twin hands Lean each touch as it came (finger, down,
    move or up; x, y; time) and the latest vsync's placement (offset,
    composer top, shift), and the keyboard's actions as they came. A
    Lean function turns them into `App.Event`s.
  - Speed: a few touches a frame, and the long-press timer already
    runs on Lean's thread once a frame. The twin-demo e2e's taps check
    it on the emulator.
  - Then provable: [`hit_iff`] and [`pinned_tap`] from the finger's
    screen row, not from a distance the C worked out; and the wanted "a
    press that turns into a scroll past the slop is not a tap". iOS
    keeps UIKit's recognizers.
- [ ] **Call the placement; don't copy it.**
  - Moves: the formulas in layer.c's `bl_place_list` and `bl_vsync`,
    and host.c's `dump`.
  - Instead: `Seam.place`, `Seam.pinned` and `Geom.composerTop`,
    exported (`@[export]`) over fixed-width integers and called by the
    vsync thread and by host.c. Sim.lean calls them too.
  - Speed: the vsync thread is not Lean's. It registers with Lean's
    runtime once (`lean_initialize_thread`, as qr's JNI does). The
    exports take and return scalars only, so a call allocates nothing
    and never waits on Lean. `bl_stats`'s missed vsyncs must stay 0 on
    the same fling, before and after.
  - Then provable: [`placed_row`], [`visible_in_viewport`] and
    [`newest_visible`] of the placement that runs. Geometry's trusted
    step goes.
- [ ] **Bound the offset in Lean.**
  - Moves: scroll.c's clamps and its rules for `scrollBy` and
    `scrollTo` (`bs_pending`), and layer.c's prediction (`bl_ahead`).
  - Instead: exported pure functions of the offset, the rate, the lead,
    the fling's end and the heights. The physics stays the OS's:
    VelocityTracker and OverScroller, and UIScrollView.
  - Speed: as for the placement, on the vsync thread.
  - Then provable: the offset Lean draws at is within the content's
    range, and during a fling between the offset now and where the
    fling stops.
- [ ] **The control channel off unless asked, and in Lean.**
  - Moves: ctl.c and ctl_ios.c (416 lines).
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
    rows copied, and `bl_stats`, on the same fling before and after; and
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

**What stays native:**
- **The OS's own APIs:** the window and the compositor (ASurfaceControl
  and AHardwareBuffer; IOSurface and Core Animation), vsync, touches as
  the OS delivers them, the keyboard (an EditText and a UITextField, so
  every input method works), the camera, the clipboard, permissions and
  the app's lifecycle, logging, and the last copy into the OS's buffers.
  Scrolling's physics stays the OS's too, so a fling feels native, as
  LAYOUT.md has it.
- **Vetted crypto:** the Rust crates, their hypotheses kept as
  hypotheses.
- **SQLite, tested as it ships.** The desktop's tests link the system's
  SQLite while phones ship 3.50.4, and glue_android.c repeats glue.c.
  One vendored SQLite and one glue file on every platform would make the
  engine's differential, crash and purge tests run what ships.
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
[`Unforgeable`]: ops/community/Laws.lean#L270-L272
[`CollisionFree`]: engine/core/Proofs.lean#L542-L544
[`Distinct`]: engine/core/Proofs.lean#L538-L540
[`lbl_inj`]: ops/sync/Fp.lean#L264-L268
[`NoSecondPreimage`]: ops/community/Merkle.lean#L137-L138
[`assumptions_hold`]: ops/community/Merkle.lean#L534-L538
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
[`joinOps_travels`]: ops/community/Intents.lean#L246-L250
[`found_travels`]: ops/community/Intents.lean#L257-L261
[`stopWaiting_local`]: ops/community/Intents.lean#L253-L254
[`filed_send`]: ops/sync/ConnLaws.lean#L175-L178
[`offer_stored`]: engine/core/Sync.lean#L98-L101
[`tick_send`]: ops/sync/ConnLaws.lean#L184-L187
[`recipients_iff`]: ops/community/Connect.lean#L214-L218
[`members_iff`]: ops/community/Connect.lean#L205-L208
[`member_opens`]: ops/community/Laws.lean#L900-L904
[`openSealed_seal`]: ops/community/Laws.lean#L890-L892
[`unbox_box`]: ops/community/Keys.lean#L89-L91
[`check_reads_shared`]: ops/community/Laws.lean#L811-L813
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
[`Codec.encode_decode`]: engine/core/Codec.lean#L154-L157
[`Op.id_decode`]: engine/core/Core.lean#L85-L87
[`distinct_of_collisionFree`]: engine/core/Proofs.lean#L546-L549
[`op_of_valid`]: ops/community/Laws.lean#L227-L232
[`Pic.decode_sized`]: engine/renderer/pic/Laws.lean#L198-L201
[`Mdns.decode_valid`]: engine/wire/mdns/Laws.lean#L540-L541
[`Community.parse_valid`]: ops/community/Link.lean#L213-L214
[`Qr.parse_valid`]: engine/renderer/qr/SegLaws.lean#L336-L338
[`chunk_is_slice`]: ops/community/Laws.lean#L673-L682
[`verify_sound`]: ops/community/Merkle.lean#L426-L432
[`complete_assembles`]: ops/community/Merkle.lean#L473-L479
[`chunk_unique`]: ops/community/Laws.lean#L735-L741
[`progress_exact`]: ops/community/Intents.lean#L493-L502
[`no_injective_hash`]: ops/community/Merkle.lean#L236-L238
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
[`sum_left`]: engine/core/Families.lean#L69-L72
[`sum_scope_left`]: engine/core/Families.lean#L75-L76
[`Codec.decode_encode`]: engine/core/Codec.lean#L148-L148
[`Op.decode_bytes`]: engine/core/Core.lean#L90-L90
[`request_valid`]: ops/community/Laws.lean#L409-L417
[`approve_valid`]: ops/community/Laws.lean#L425-L433
[`admit_admits`]: ops/community/Laws.lean#L441-L452
[`connect_admitted`]: ops/community/Connect.lean#L169-L179
[`removeMember_valid`]: ops/community/Intents.lean#L375-L382
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
[`place_shows`]: engine/renderer/TextLaws.lean#L63-L65
[`place_starts`]: engine/renderer/TextLaws.lean#L128-L134
[`digits_keep_order`]: engine/renderer/TextLaws.lean#L109-L116
[`message_read`]: ops/community/message/ViewLaws.lean#L61-L66
[`profile_read`]: ops/community/message/ViewLaws.lean#L39-L41
[`profile_authorized`]: ops/community/Laws.lean#L307-L314
[`no_renaming`]: ops/community/Laws.lean#L321-L332
[`name_placed`]: ops/community/reaction/RowLaws.lean#L89-L92
[`oneLine_prefix`]: engine/renderer/TextLaws.lean#L97-L98
[`controls_neutral`]: engine/renderer/TextLaws.lean#L153-L157
[`marks_invisible`]: engine/renderer/TextLaws.lean#L159-L159
[`time_shown`]: ops/community/reaction/RowLaws.lean#L84-L87
[`tally_nodup`]: ops/community/reaction/RowLaws.lean#L56-L60
[`tally_mem`]: ops/community/reaction/RowLaws.lean#L68-L71
[`picBox_aspect`]: ops/community/reaction/RowLaws.lean#L19-L28
[`readable_held`]: ops/community/Intents.lean#L295-L299
[`readable_complete`]: ops/community/Intents.lean#L337-L341
[`switcherOrder_sound`]: ops/app/Pages.lean#L656-L658
[`switcherOrder_complete`]: ops/app/Pages.lean#L663-L665
[`dedupe_nodup`]: ops/app/Switch.lean#L52-L53
[`dedupe_one_per_community`]: ops/app/Switch.lean#L56-L58
[`select_tapped_dedupe`]: ops/app/Switch.lean#L82-L84
[`drawPage_key`]: App.lean#L874-L878
[`pageIn_acc`]: App.lean#L880-L883
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
