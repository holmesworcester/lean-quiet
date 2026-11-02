# What the proofs caught

Bugs a law found: a proof that stopped checking on a change, or a law
whose statement turned out false of the code. Each entry says what
broke, how the law noticed, the fix, and what keeps it caught (a
negative control, a test). When a law catches something, add it here
and keep the code as it was as a `control` in tests/wiring.txt.

Bugs found some other way and pinned by a law afterwards are listed
apart, at the end: there the law came second.

The gate (`ci/local.sh`) is the proofs and a few fast, deterministic
tests; the rest (`ci/local.sh --full`) runs nightly and before a release.
A bug the full run, dogfooding or a user finds that the gate missed is an
escape. It goes at the end with the law that now catches it, so the gate
catches it next time. The aim is no escapes.

## Caught by a law

### A user's own write could wait behind the reader's backlog (2026-11-01)

- **Bug.** The reader's pass promised (ActsLaws' `acts_shown`, over the
  RWorld model) that the wants a user's act touched are read in the same
  pass, however long the backlog. When the reader moved to a persistent
  Demand queue, `Reader.pass` queued its marked wants with
  `Demand.reconcile` alone: work queued in earlier passes kept its place
  ahead of the act's wants, and `take` treats "touched" and "visible"
  alike. With a backlog of `cap` (64) or more visible wants queued, the
  user's own message, reaction or name could wait passes to show.
- **How the law noticed.** Porting `acts_shown` from the model to the
  running pass (no proofs over models): stated over `Reader.pass`'s queue,
  it was false (`Demand.shipped_late`: a want queued earlier is taken
  before the act's).
- **Fix.** `Demand.reconcileFirst`: the act's wants ahead of the rest.
  `take_first`: while one is queued, every take returns one;
  `take_sorted`: the queue stays act-first.
- **Kept caught by.** The shipped order is `Demand.reconcileShipped`, a
  `control` in tests/wiring.txt, and `shipped_late` proves it reads the
  backlog first.

### Back to the switcher lost its backdrop (566e566, 2026-10-31)

- **Bug.** 566e566 ("Match the shared mobile community switcher to
  Quiet design") made `App.openSt` compose the switcher's backdrop when
  the switcher opens, and set it to `#[]` when any other page opens.
  The switcher's gear (community settings), Join a community, Create a
  community and Add members all open a page over the switcher. So
  switcher → gear → back drew the switcher over the plain background,
  without the dimmed screen behind it (App.lean's `shade` falls back to
  `bgRow` when the backdrop is empty).
- **How the law noticed.** `NavLaws.back_open` (**Back goes back**:
  back after opening a page gives the state before, but for what back
  clears) stopped proving. Its `rfl` timed out (`whnf`, 200000
  heartbeats) trying to equate the composed backdrop with the old one,
  and the statement was in fact false: `shipped_back_open_fails`
  proves it fails from every state that holds a backdrop. Because
  tests/Axioms.lean imports NavLaws, the whole axiom audit failed at
  566e566, and `lake build` with it. The commit had been pushed to main
  without running `mise run check`. An audit of the proofs, rerunning
  tests/check.sh at the head, found it.
- **Then the law was loosened instead.** Before this fix landed,
  55f00be got the build green again by excepting `switcherBackdrop`
  from `back_open`'s statement, and kept the code. The law then held of
  a bug: main still drew the switcher over the plain background after
  gear → back. A failing law is a finding about the code until shown
  otherwise; changing its statement needs the same review as changing
  what users are promised.
- **Fix.** `openSt` keeps the backdrop when it opens any page but the
  switcher (`open_keeps_backdrop`). `back_open` now holds exactly for
  every page but the switcher, and `back_open_all` covers the switcher
  too: back from it keeps the backdrop it composed, which only the
  switcher draws.
- **Kept caught by.** `NavLaws.openStShipped`, `openSt` as 566e566
  shipped it, is a `control` in tests/wiring.txt, and
  `shipped_back_open_fails` proves it breaks `back_open`. The headless
  `mobile_switcher` test (tests/app/mobile_switcher.sh) taps the gear
  and then back through `App.onTap`, and checks the backdrop survives.
  Run against the shipped `openSt`, it fails.
- **Lesson.** The law states the whole state after back
  (`backSt (openSt p s) = { s with … }`), not a few fields. So a field
  added later, which nobody thought of as navigation, still falls under
  it. That is why the law caught this.

### A replayed handshake retired a live session (found 2026-10-28; fix not on main)

- **Bug.** Replaying a request whose session had been closed and purged
  makes its responder answer afresh. `kept` (app/connection/Commands.lean)
  keeps one session per peer, the newest, so the replay retires the
  live session for one no other node holds. So anyone who recorded an
  earlier handshake on the network could retire a live session.
- **How the law noticed.** Stating the pair laws over the running
  two-node world (fd/pair-secrecy, 8a4d220): the replay law was false,
  and tests/engine/PairWorld.lean on that branch pins it as a finding.
- **Fix.** 63a2c8f on fd/pair-secrecy: a session that has heard its
  peer is retired only for another that has (`kept_heard`,
  `kept_unheard`), with a `mutantKept` negative control.
- **Status at 566e566.** Not merged. Main's `kept` is still
  newest-wins.

### A crash kept a session's keys in the store for good (found 2026-10-31)

- **Bug.** `onFrame` stores a dialer's connection, then its arrival
  record, in two writes. `retired` (app/Commands.lean) read
  the sessions through `allSessions`, which places a session by that
  arrival record. A dialer that crashed between the two writes booted
  holding a session that was neither open nor retired. Nothing ever
  closed it, so its transport keys and its ephemeral stayed in the
  store for good, and `connectedTo` kept the node from dialing again.
- **How the law noticed.** README's "a closed session's keys cannot be
  recovered" was 🟡 because no law said the key-bearing ops go. The
  user asked to broaden the statement until it failed: "no row of the
  store holds key material of a session that has ended, by any path".
  Proving `retired_complete` (every established session is kept open or
  retired) failed on exactly this state.
- **Fix.** `retired` reads the established facts themselves, so every
  one not kept open is retired, and `closing` names a connection even
  once it is gone. `close_forgets`, `purge_forgets` and `forget_stays`
  then say no row holds the session's ephemeral or transport keys after
  it ends. They are proven over the running purge (the purge bridge,
  fd/purge-bridge), assuming SQLite's deletes leave no byte on disk.
- **Kept caught by.** `Connection.retiredShipped`, a `control` in
  tests/wiring.txt, and `shipped_retired_misses`, which proves the
  shipped rule leaves that session with neither.
  tests/engine/ConnectionCheck.lean (`crashedDial`) runs it on SQLite:
  two nodes, the dialer's arrival record lost, its node rebooted. The
  keys go, and with the shipped rule they stay.

## Found otherwise, pinned by a law afterwards

- **A room shown mid-session waited for the dialer's 30 s timer**
  (seen by the user as slow syncing "in some cases. maybe because the
  connecting peer", 2026-11-01). Until event rounds, only the dialer
  opened rounds, on one timer per connection (`Conn.work`,
  `c.dialer && c.lastRound + cfg.every ≤ now`), and `Conn.setRooms`
  added a newly visible room without opening a round in it. So a room
  that became visible mid-session (a join just approved, a new room)
  waited up to 30 s, and the responder could not ask; a have for a room
  the peer did not list yet was ignored too. Now a room a session
  starts showing is due (`shown_due`): the dialer's next tick opens its
  round (`round_due`), and the responder asks with an empty have naming
  it (`responder_asks`), which makes the dialer open it (`ask_due`,
  `join_round`). The shipped `Conn.work` is kept as the control
  `Conn.workShipped` in tests/wiring.txt: `shipped_responder_silent`
  and `shipped_dialer_waits` prove it breaks `responder_asks` and
  `round_due` (`shipped_controls_apply` on a concrete session).
  tests/engine/LiveRounds.lean runs it on two SQLite nodes: the joiner's
  history arrives within one tick of its admission, either way round;
  its `main-cadence` mutant (tests/engine/simplify_negative.py) leaves
  the joining responder waiting.

- **The removal-notice fix held quota on every drained close** (found by
  the release run's engine:ingress, 2026-11-01: `ingress_tcp` 62/6 every
  run). `Tcp.linger`, the fix below, ran on every drained close, not only a
  removal's: a drain with nothing to deliver (a silence expiry, say) waited
  up to `stallMs` for its peer's end before releasing its socket's quota.
  Now a drain lingers only on a socket the same step sent final frames to.
  Pinned by laws: `Outbox.drain_lingers`, `drain_quiet_closes` (a drain
  without final frames never lingers) and `stopped_never_lingers`, of the
  `Outbox.lingers` the writer reads, all in tests/Axioms.lean.

- **A removed member could miss its removal notice** (found as a gate
  "flake", 2026-11-01: expiry-grace's "actual retirement writer drains
  the signed removal notice to its peer" failed about one run in six
  under load, on main too). The retiring side wrote the notice, then
  shut its socket in both directions (`SocketAbort.abort`). The removed
  peer, still replying to earlier frames, wrote again; Linux answers a
  segment to a read-shut socket with a reset, the peer's writer failed,
  and a failed writer stops its reader: the notice it had not yet read
  was dropped (a socket trace showed the reader cut off mid-frame).
  Now a retirement ends with a FIN and reads until the peer's own end,
  within `stallMs` (`Tcp.linger`). Pinned by a test, not yet a law:
  tests/engine/EpochIngress.lean keeps the peer writing after the
  retirement and checks its writer survives; the shipped close, its
  control in tests/engine/expiry_grace_negative.py, fails it and the
  notice check every run.

- **Every checkpoint the app ever saved stayed on disk** (found by an
  audit hunting promises narrower than they read, 2026-10-31).
  `Lifecycle.save` only inserted into `app_ops`. Each row holds invite
  links with their bearer seeds, drafts with their photos, and queued
  writes (a found or join's device seed, node secret and content key),
  and a row was added every committed frame. Now saving deletes the
  older rows in the same transaction. Pinned by a test, not yet a law:
  tests/engine/Purge.lean's `checkpointRows` finds no byte of a
  forgotten secret, and the old INSERT, its control, keeps it.

- **The switcher selected the wrong community** when two had the same
  name (seen on an iPhone). A tapped row was matched back to
  its entry by short id and name, so twins always landed on the first.
  Fixed in 03d33a9: rows carry their index, and `switcherOrder_sound`,
  `switcherOrder_complete` and `dedupe_nodup` now hold.
- **A photo's decode ran on every frame**, stalling the Pixel for
  seconds. The cost law `imageV_over_budget` keeps the shipped `image`
  (`Pics.imageV`) as a negative control over the frame's budget.
- **Members were told "You've been removed" when no one removed them**
  (found by the gate's pixel test, 2026-11-01; an escape until then: the
  same frame had passed as a flake). Opening the switcher over sixteen
  new communities showed "You've been removed from Community 16" in
  about one run in six under load. `Accepted.read` marked an entry
  removed when its admission was read but a second read, of whether its
  device was live, found none; the two reads need not see the same store.
  A wrongly removed entry also forgot its composer text, invite link and
  profile, and was remembered as told, so a real removal later would go
  untold. Fixed: removed now needs a removal read (`deviceCut`), and
  `deviceCut_removal` proves it holds only with a removal in the store
  it read, whatever an earlier read saw. The shipped
  mark is kept as `PeopleLaws.removedShipped`, a `control` in
  tests/wiring.txt, and `shipped_removed_without_removal` proves it marks
  an entry removed with no removal read.
- **A command's "authoritative snapshot" was a read at a time** (found
  by the gate's pixel test under load, 2026-11-01, by several sessions:
  "You're in." over a founder's pages, "visual key missing", cases whose
  pixels changed run to run). `transaction`, the one-shot reader every
  command uses (`intentView`, `refreshCommsNow`), ran its reads on the
  frame's connection without a transaction of its own: inside a frame
  they shared the frame's snapshot, but a command run outside one (a
  fixture, a lifecycle handler) read the store as of each read, with
  the writer committing between them. `Accepted.read` then found the
  founder's admission in one list and not in the next, so its entry
  looked waiting and the frame said "You're in." when it was read again.
  Fixed: `transaction` opens a savepoint, a read transaction of its own
  when none is open and nested in the frame's when one is. All 72 pixel
  cases, 24 runs at once: 4 cases changed run to run and 3 runs lost the
  key before the fix; none after. Pinned by a test, not yet a law.
- **Stage 3b's reader-act send lost what made an own send show at once**
  (found by `component_demand`, a `--full` test, when it began failing
  after main 9e34c393; bisected by holmes-27, so an escape: the gate passed
  stage 3b). Three bugs, one fix each:
  1. Placements were taken a frame early. The reader publishes a send's
     placements and its result in one pass, but `applyDone` drained the
     placements every frame and `takeDone` took the results only at the
     next frame's top. A send's placements were gone when its result came,
     so no own send was ever pinned. Now `takeDone` and `parkDone` take the
     placements with the results, into `placedQ` (by act id).
  2. A burst of sends lost its common root. Each act's intent read through
     the reader's cache, which no notice had told of the pass's earlier
     acts (the pass notices after its acts, to mark what they touch). The
     second send in a pass did not see the first as pending, so it started
     its own thread. Now an act's intent reads with no cache: the store and
     the outbox, as the frame's `writeAll` did.
  3. A background step dropped finished acts. `backgroundStep` took the
     reader's results and discarded them, so their continuations never ran
     and `wait` never went idle. Now it queues them for the next frame, as
     a frame does.
  The test's first failure, "optimistic bitmap missing", was not one of
  these: it founded, opened chat and sent in one frame, and founding is
  now an act, so the found's continuation moved it to the new community's
  home. The test now waits for the found, and `Presentation`'s checks wait
  for the sends (`settleSends`) and read the reader's outbox. Pinned by a
  test, not yet a law: `component_demand` (82 checks).
