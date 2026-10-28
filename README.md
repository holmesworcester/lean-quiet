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
  - `engine/Tests/Purge.lean` reads the database's files raw and finds no
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
- **All 194 rest on Lean's standard axioms only:** no `sorry` and no
  added axiom, as each part's `tests/check.sh` checks.
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
| 🟡 | 🥊🥊🥊 | **A closed session's keys cannot be recovered,** from the disk or from the static keys later. Proven: with the ephemerals gone, both static keys and the whole transcript do not give the session keys, and the session's rows are gone. Tested: no file of the database holds a byte of them (`engine/Tests/Purge.lean`). Wanted: that closing purges every ephemeral (`close_forgets`). | [`kk_forward_secret`], [`kk_forward_secret_init`], [`kk_forward_secret_resp`], [`purge_gone`], [`purge_named`] |
| ⬜ | 🥊🥊🥊 | **Session secrets never reach the disk.** They would be ephemeral ops, held in memory, so forward secrecy would not rest on deletion. A restart then redials. | |
| ⬜ | 🥊🥊🥊 | **Removed members cannot read new messages.** This needs key rotation, which is not built. | |
| ⬜ | 🥊🥊 | **Every offered id names a stored op in one of the peer's rooms** (`have_shown`). This is the disclosure law for ids. | |
| | | **Connections** | |
| ✅ | 🥊🥊🥊 | **The trust rule lets in exactly the live members.** Read from the node's tables, it accepts exactly the devices of admitted, unremoved users. Nodes that hold the same ops agree on it. | [`connect_iff`], [`refuse_nonmember`], [`connect_approved`], [`connect_agree`] |
| ✅ | 🥊🥊🥊 | **A removal cuts the removed user out of the rule.** Once a node holds it, the rule refuses every device of that user. Only an admin can remove another user, and nothing undoes it. | [`removal_cuts_off`], [`removals_iff`], [`removal_authorized`], [`removed_stays`] |
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
| ⬜ | 🥊🥊🥊 | **The running connection does all this.** It performs the round, and delivers each op's requirement closure (`conn_runs_exchange`, `closure_delivered`). This retires `net/`'s model. | |
| ⬜ | 🥊🥊🥊 | **New ops reach connected members.** An op stored while a member's connection is up is offered on it at once, if the member may see its room. The member holds it after one exchange (`stream_delivers`). Tested, not proven. | |
| ⬜ | 🥊🥊🥊 | **Everyone converges.** Under fair delivery, members linked by any chain of connections eventually hold every op of their community. By [`same_ops_same_verdicts`], they then hold the same verdicts. Proven so far for two nodes, over a model. | |
| ⬜ | 🥊🥊 | **Staleness is never hidden.** What the screen says about sync is true of the ops held. "Up to date as of T" means a round the device opened at its own time T ended with it holding everything the peer held in that room. If no round ends within a stated bound, the screen says so within that bound. | |
| ⬜ | 🥊🥊🥊 | **A synced page is complete:** after syncing a page, a device shows every row its peer shows for it (`page_sync`). | |
| ⬜ | 🥊🥊 | **Sync is efficient.** Each op is sent at most once per connection, and a round needs at most fan·Δ·⌈log n⌉ claims. | |
| ⬜ | 🥊 | **The cached Merkle tree's labels are `lbl`'s,** for O(log n) fingerprints with no change on the wire. | |
| | | **The screen** | |
| ✅ | 🥊🥊🥊 | **Nothing on screen is covered or mis-tapped.** Content in the viewport is drawn below the header, and above the composer and keyboard. Pinned to the bottom, the newest message is wholly visible. A tap lands on the row, or emoji key, drawn under it. | [`visible_in_viewport`], [`newest_visible`], [`pinned_visible`], [`pinned_tap`], [`hit_iff`] |
| ✅ | 🥊🥊🥊 | **A screen re-reads only what changed.** A list changes only when a row is filed under a key it read, and no list holds an op twice. | [`eval_stable`], [`view_stable`], [`filed_rel`], [`mem_keysOf`], [`matching_nodup`] |
| ✅ | 🥊🥊🥊 | **Removing someone takes two confirmations.** Nothing is written before the second, and cancelling writes nothing. Each attempt starts fresh, and one in flight cannot be replaced. The action is offered only to an admin, on another present member. | [`writes_only_after_two`], [`cancel_writes_nothing`], [`open_fresh`], [`no_replace`], [`offered_only`] |
| ✅ | 🥊🥊 | **The people list is the present members,** each once. A removed member leaves it and its count, but keeps their name on their messages. | [`present_iff`], [`present_nodup`] |
| ⬜ | 🥊🥊🥊 | **The screen is one moment.** Every frame is the root component drawn over a single settled store state, the latest the app has seen, so if one row is current, all are. Half of this is proven: a cached component whose keys did not fire answers as a fresh read would. Wanted: the renderer re-reads exactly what fired, and reads only between write turns. | [`eval_stable`], [`view_stable`], [`drain_bounded`] |
| ⬜ | 🥊🥊 | **An action's toast stays until the screen shows it.** A toast for an action (removing someone, a new name or avatar) stays up until every component on screen has re-read a state that holds the action's op, or until the OS's toast time passes, whichever comes first. So a toast that leaves early proves the screen has caught up. | |
| ✅ | 🥊🥊 | **The layout is exact.** The slide and keyboard shift are exact, and page rows are where the page put them. Emoji keys never overlap, and every key is reachable. An invite's hints and QR fit, and the camera preview reads inside its frame. | [`placed_row`], [`newest_drawn`], [`pinned_row`], [`keys_disjoint`], [`hit_cell`], [`reachable`], [`compose_row`], [`compose_top`], [`Link.hints_fit`], [`Link.qr_fits`], [`Camera.src_in`] |
| 🟡 | 🥊🥊🥊 | **Message text is shown faithfully.** A row's glyphs, read in order, are exactly the body's visible characters. Nothing is clipped, reordered or taken from another row, and every line fits. Proven: wrapping drops only spaces and keeps every other character in order, and every line fits when every character does; bidi reordering is a permutation (nothing dropped or invented); the glyphs placed are exactly the visible characters, each starting where the one before ends; numbers keep their order inside right-to-left text, for the reported cases. Wanted: that order in general, and `layout` as one statement over the three. | [`wrap_keeps`], [`wrap_fits`], [`visual_perm`], [`place_shows`], [`place_starts`], [`digits_keep_order`] |
| 🟡 | 🥊🥊🥊 | **Names are shown correctly.** A message row draws its author's name, as the views pick it, and no one else's. No bidi override or invisible character can disguise a name or a message. Proven: a row's name is its author's newest valid profile's (or "…"), and only a device admitted into that user can have written it; the row draws it cut to a logical prefix and an ellipsis, so a long name keeps its beginning in either direction. Bidi controls are neutrals in the running bidi, so they reorder nothing; that is not yet a theorem. | [`message_read`], [`profile_read`], [`profile_authorized`], [`no_renaming`], [`name_placed`], [`oneLine_prefix`] |
| ✅ | 🥊🥊 | **Times, reactions and pictures are shown as held:** the claimed time's clock, each reaction's count of distinct reactors, and each picture at its aspect inside its box. One pill per emoji, whose reactors are exactly who reacted with it, each once; a picture's box has one side at its bound and the other scaled by its aspect. | [`time_shown`], [`message_read`], [`tally_nodup`], [`tally_mem`], [`picBox_aspect`] |
| 🟡 | 🥊🥊🥊 | **What you see is what was sent.** The rows a device draws are the views of the facts its ops hold, from network to pixel. Proven, over a model where every list read is the engine's: a shown message is a valid fact of the store, and its row's name, time and text are its author's name, its claimed time and its body opened with a key the store holds; the conversation is exactly the messages under keys this device holds. Wanted: the same from the row's layout to its pixels. | [`message_read`], [`readable_held`], [`readable_complete`], [`eval_stable`] |
| ✅ | 🥊🥊🥊 | **Every community is reachable, and is one entry.** A switcher row's tap selects exactly the entry it draws, every entry has a row, no two entries share an acceptance or a community, and a page is drawn from its key alone, which names its entry's op, never a name. | [`switcherOrder_sound`], [`switcherOrder_complete`], [`dedupe_nodup`], [`dedupe_one_per_community`], [`select_tapped_dedupe`], [`drawPage_key`], [`pageIn_acc`] |
| ⬜ | 🥊🥊 | **The screen keeps up:** no blank rows past a latency bound, within a frame budget, with bounded reads. | |
| ⬜ | 🥊🥊 | **Display order** (design in `engine/docs/SYNC.md`). Devices with the same ops order messages alike, except a saturated tail, which follows receipt order. | |
| | | **Codes, pictures and discovery** | |
| ✅ | 🥊🥊 | **What the encoders write reads back.** This holds for QR segments and codewords, invite links and mDNS packets. QR error correction is sound, and format and version readings tolerate their designed bit errors. | [`parse_segsBits`], [`parse_dataStream`], [`RS.correct_sound`], [`RS.correct_clean`], [`decodeFormat_correct`], [`decodeVersion_correct`], [`parse_text`], [`Base62.decode_encode`], [`Mdns.decode_encode`], [`decode_roundtrip`] |
| ✅ | 🥊 | **Pictures render whole:** scaled and composited pictures are well-formed and opaque, and the tray's layout fits. | [`render_wellFormed`], [`render_opaque`], [`scale_wellFormed`], [`fit_round`], [`layout_inside`], [`layout_apart`] |

The theorems not listed here are lemmas. Each part's axiom audit lists
them all: `tests/Axioms.lean` or `tests/axioms.lean`.

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
  some. Then it checks the README's theorem links (`readme`). Logs go
  to `out/ci/`.
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

<!-- proof-links: written by ci/proof-links.py; do not edit -->
[`Unforgeable`]: engine/Community/Laws.lean#L249-L251
[`CollisionFree`]: engine/Engine/Proofs.lean#L515-L517
[`Distinct`]: engine/Engine/Proofs.lean#L511-L513
[`lbl_inj`]: engine/Engine/Sync/Fp.lean#L264-L268
[`Suite.Good`]: engine/Connection/Noise.lean#L49-L53
[`Keys.Good`]: engine/Connection/Types.lean#L32-L36
[`no_impersonation`]: engine/Community/Laws.lean#L268-L281
[`admission_needs_approval`]: engine/Community/Laws.lean#L448-L456
[`admission_approved`]: engine/Community/Laws.lean#L367-L377
[`request_invited`]: engine/Community/Laws.lean#L331-L341
[`removal_authorized`]: engine/Community/Laws.lean#L483-L486
[`admin_granted`]: engine/Community/Laws.lean#L522-L523
[`removed_stays`]: engine/Community/Laws.lean#L529-L532
[`valid_stays`]: engine/Community/Laws.lean#L536-L540
[`message_authorized`]: engine/Community/Laws.lean#L234-L240
[`approval_signed`]: engine/Community/Laws.lean#L350-L360
[`invitation_issued`]: engine/Community/Laws.lean#L316-L322
[`named_by_admin`]: engine/Community/Laws.lean#L574-L576
[`admission_consented`]: engine/Community/Laws.lean#L253-L259
[`admin_removal_stands`]: engine/Community/Laws.lean#L494-L507
[`mutual_removal`]: engine/Community/Laws.lean#L515-L519
[`removed_approver_admits`]: engine/Community/Laws.lean#L467-L478
[`recv_send`]: engine/Engine/Sync/ConnLaws.lean#L146-L148
[`offer_shared`]: engine/Engine/Sync.lean#L83-L86
[`wire_kinds`]: engine/Connection/Laws.lean#L35-L36
[`local_kinds`]: engine/Connection/Laws.lean#L42-L43
[`joinOps_travels`]: engine/Community/Intents.lean#L226-L230
[`found_travels`]: engine/Community/Intents.lean#L237-L241
[`stopWaiting_local`]: engine/Community/Intents.lean#L233-L234
[`filed_send`]: engine/Engine/Sync/ConnLaws.lean#L175-L178
[`offer_stored`]: engine/Engine/Sync.lean#L98-L101
[`tick_send`]: engine/Engine/Sync/ConnLaws.lean#L184-L187
[`recipients_iff`]: engine/Community/Connect.lean#L214-L218
[`members_iff`]: engine/Community/Connect.lean#L205-L208
[`handshake_agrees`]: engine/Connection/Noise.lean#L313-L325
[`sent1_write1`]: engine/Connection/Noise.lean#L219-L222
[`sent1_read1`]: engine/Connection/Noise.lean#L251-L257
[`read2_write2'`]: engine/Connection/Noise.lean#L290-L295
[`purge_gone`]: engine/Engine/Purge.lean#L261-L263
[`purge_named`]: engine/Engine/Purge.lean#L267-L271
[`connect_iff`]: engine/Community/Connect.lean#L146-L150
[`refuse_nonmember`]: engine/Community/Connect.lean#L161-L164
[`connect_approved`]: engine/Community/Connect.lean#L182-L193
[`connect_agree`]: engine/Community/Connect.lean#L226-L229
[`removal_cuts_off`]: engine/Community/Connect.lean#L241-L245
[`removals_iff`]: engine/Community/Connect.lean#L43-L44
[`recv_take`]: engine/Engine/Sync/ConnLaws.lean#L118-L120
[`no_connection_before_approval`]: net/Net/Laws.lean#L39-L46
[`sessions_trusted`]: net/Net/Laws.lean#L63-L68
[`intake_local`]: engine/Engine/Sync.lean#L41-L43
[`stored_local`]: engine/Engine/Sync.lean#L137-L140
[`local_fact_mine`]: engine/Community/Laws.lean#L593-L597
[`intakeConn_conn`]: engine/Engine/Sync.lean#L36-L37
[`established_agrees`]: engine/Connection/Laws.lean#L46-L56
[`open_seal`]: engine/Connection/Frame.lean#L51-L55
[`cid_seal`]: engine/Connection/Frame.lean#L79-L82
[`Codec.encode_decode`]: engine/Engine/Codec.lean#L154-L157
[`Op.id_decode`]: engine/Engine/Core.lean#L85-L87
[`distinct_of_collisionFree`]: engine/Engine/Proofs.lean#L519-L522
[`Pic.decode_sized`]: qr/Pic/Laws.lean#L198-L201
[`Mdns.decode_valid`]: mdns/Mdns/Laws.lean#L540-L541
[`Community.parse_valid`]: engine/Community/Link.lean#L213-L214
[`Qr.parse_valid`]: qr/Qr/SegLaws.lean#L336-L338
[`drain_bounded`]: engine/Engine/Budget.lean#L174-L179
[`drain_terminates`]: engine/Engine/Termination.lean#L84-L87
[`step_budget`]: engine/Engine/Budget.lean#L135-L137
[`same_ops_same_verdicts`]: engine/Engine/Termination.lean#L118-L126
[`order_free`]: engine/Engine/Proofs.lean#L607-L612
[`drain_settles`]: engine/Engine/Termination.lean#L110-L114
[`status_iff_spec`]: engine/Engine/Proofs.lean#L456-L458
[`spec_extends`]: engine/Engine/SpecLemmas.lean#L137-L139
[`inv_ingest`]: engine/Engine/Proofs.lean#L207-L207
[`inv_step`]: engine/Engine/Proofs.lean#L238-L238
[`purge_shared`]: engine/Engine/Purge.lean#L274-L276
[`purge_settles`]: engine/Engine/Budget.lean#L203-L209
[`purge_undecides`]: engine/Engine/Proofs.lean#L352-L359
[`purge_inv`]: engine/Engine/Proofs.lean#L367-L371
[`mem_purgeSet`]: engine/Engine/Proofs.lean#L340-L344
[`reach_ops`]: engine/Engine/Proofs.lean#L597-L599
[`sum_left`]: engine/Engine/Families.lean#L69-L72
[`sum_scope_left`]: engine/Engine/Families.lean#L75-L76
[`Codec.decode_encode`]: engine/Engine/Codec.lean#L148-L148
[`Op.decode_bytes`]: engine/Engine/Core.lean#L90-L90
[`request_valid`]: engine/Community/Laws.lean#L388-L396
[`approve_valid`]: engine/Community/Laws.lean#L404-L412
[`admit_admits`]: engine/Community/Laws.lean#L420-L431
[`connect_admitted`]: engine/Community/Connect.lean#L169-L179
[`exchange_complete`]: engine/Engine/Sync/RoundLaws.lean#L232-L241
[`opening_honest`]: engine/Engine/Sync/RoundLaws.lean#L323-L325
[`num_inj`]: engine/Engine/Sync/Fp.lean#L37-L37
[`spec_local`]: engine/Engine/Sync/Locality.lean#L54-L58
[`bootstrap`]: net/Net/Laws.lean#L401-L405
[`bootstrap_ideal`]: net/Net/Laws.lean#L423-L424
[`bootstrap_possible`]: net/Net/Laws.lean#L208-L218
[`reachable_inv`]: net/Net/Steps.lean#L222-L223
[`visible_in_viewport`]: app/Quiet/Geometry.lean#L90-L95
[`newest_visible`]: app/Quiet/Geometry.lean#L99-L105
[`pinned_visible`]: app/Quiet/Geometry.lean#L147-L151
[`pinned_tap`]: app/Quiet/Geometry.lean#L154-L157
[`hit_iff`]: app/Quiet/SheetGeom.lean#L93-L95
[`eval_stable`]: engine/Engine/View.lean#L137-L142
[`view_stable`]: engine/Engine/View.lean#L163-L165
[`filed_rel`]: engine/Engine/Decl.lean#L163-L170
[`mem_keysOf`]: engine/Engine/Decl.lean#L79-L82
[`placed_row`]: app/Quiet/Geometry.lean#L81-L85
[`newest_drawn`]: app/Quiet/Geometry.lean#L108-L111
[`pinned_row`]: app/Quiet/Geometry.lean#L141-L144
[`keys_disjoint`]: app/Quiet/SheetGeom.lean#L148-L150
[`hit_cell`]: app/Quiet/SheetGeom.lean#L144-L146
[`reachable`]: app/Quiet/SheetGeom.lean#L165-L168
[`compose_row`]: app/Quiet/SheetGeom.lean#L189-L193
[`compose_top`]: app/Quiet/SheetGeom.lean#L199-L202
[`Link.hints_fit`]: app/Quiet/Link.lean#L49-L51
[`Link.qr_fits`]: app/Quiet/Link.lean#L67-L67
[`Camera.src_in`]: app/Quiet/Camera.lean#L51-L53
[`wrap_keeps`]: app/Quiet/WrapLaws.lean#L132-L135
[`wrap_fits`]: app/Quiet/WrapLaws.lean#L206-L209
[`visual_perm`]: app/Quiet/TextLaws.lean#L46-L47
[`place_shows`]: app/Quiet/TextLaws.lean#L63-L65
[`place_starts`]: app/Quiet/TextLaws.lean#L128-L134
[`digits_keep_order`]: app/Quiet/TextLaws.lean#L109-L116
[`message_read`]: app/Quiet/ViewLaws.lean#L61-L66
[`profile_read`]: app/Quiet/ViewLaws.lean#L39-L41
[`profile_authorized`]: engine/Community/Laws.lean#L286-L293
[`no_renaming`]: engine/Community/Laws.lean#L300-L311
[`name_placed`]: app/Quiet/RowLaws.lean#L89-L92
[`oneLine_prefix`]: app/Quiet/TextLaws.lean#L97-L98
[`time_shown`]: app/Quiet/RowLaws.lean#L84-L87
[`tally_nodup`]: app/Quiet/RowLaws.lean#L56-L60
[`tally_mem`]: app/Quiet/RowLaws.lean#L68-L71
[`picBox_aspect`]: app/Quiet/RowLaws.lean#L19-L28
[`readable_held`]: engine/Community/Intents.lean#L275-L279
[`readable_complete`]: engine/Community/Intents.lean#L317-L321
[`switcherOrder_sound`]: app/Quiet/Pages.lean#L583-L585
[`switcherOrder_complete`]: app/Quiet/Pages.lean#L590-L592
[`dedupe_nodup`]: app/Quiet/Switch.lean#L52-L53
[`dedupe_one_per_community`]: app/Quiet/Switch.lean#L56-L58
[`select_tapped_dedupe`]: app/Quiet/Switch.lean#L82-L84
[`drawPage_key`]: app/Quiet/App.lean#L795-L799
[`pageIn_acc`]: app/Quiet/App.lean#L801-L804
[`parse_segsBits`]: qr/Qr/SegLaws.lean#L157-L161
[`parse_dataStream`]: qr/Qr/SegLaws.lean#L193-L197
[`RS.correct_sound`]: qr/Qr/Laws.lean#L55-L57
[`RS.correct_clean`]: qr/Qr/Laws.lean#L74-L76
[`decodeFormat_correct`]: qr/Qr/Format.lean#L104-L105
[`decodeVersion_correct`]: qr/Qr/Format.lean#L113-L116
[`parse_text`]: engine/Community/Link.lean#L197-L198
[`Base62.decode_encode`]: engine/Community/Link.lean#L133-L133
[`Mdns.decode_encode`]: mdns/Mdns/Laws.lean#L289-L290
[`decode_roundtrip`]: mdns/Mdns/Laws.lean#L584-L587
[`render_wellFormed`]: qr/Pic/Laws.lean#L219-L219
[`render_opaque`]: qr/Pic/Laws.lean#L222-L226
[`scale_wellFormed`]: qr/Pic/Laws.lean#L236-L236
[`fit_round`]: qr/Pic/Laws.lean#L87-L90
[`layout_inside`]: qr/Pic/Laws.lean#L170-L172
[`layout_apart`]: qr/Pic/Laws.lean#L147-L148
<!-- /proof-links -->
