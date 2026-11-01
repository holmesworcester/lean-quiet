# Peer endpoints: implementation and verification

Branch `peer-endpoints`, merged with `origin/main` (op tree). No iroh. This report
says what is proved, what is assumed, what the real-network tests showed, and
what is still open. The README's [peer endpoints](../README.md#peer-endpoints-and-discovery)
section is the short form.

## What runs

- **Invite addresses.** An invite carries up to eight LAN/tailnet IPv4 hints
  (Docker bridges excluded; a tailnet slot reserved after the first LAN address).
  A pending join dials one hint per attempt, rotating, under its retry clock.
- **Endpoint ops.** `addresses` (shared, signed by the member's admitted device,
  at most eight hints, lifetime at most a day; the newest supersedes, expired or
  not) and `sighting` (shared, signed: where a member saw another node, with that
  node's authenticated listening port). A member republishes on change (60 s
  apart) or at half the lifetime. A sighting is written only for an address the
  node does not already publish.
- **Discovery.** LAN DNS-SD (multicast on explicit LAN interfaces), and unicast
  DNS-SD queries to known tailnet addresses on UDP 5353 with QU answers (RFC 6762
  §5.5), because Tailscale does not carry multicast. Results become local
  `discovered` ops for known node keys only.
- **One dial path.** Invite hints, publications and DNS-SD observations feed one
  planner: at most 24 candidates, one attempt per visit, a per-node retry clock
  (local `retry` op) with backoff capped at 60 s that no advertisement can reset.
  The dialer scans pending joins and members two rows per tick with a cursor in a
  local `scan` op that also records the node keys it visited.
- **A winner.** Of simultaneous attempts, one from each side, both ends keep the
  session with the least connection-op id, which both hold after the two-message
  handshake: no extra round trip. Within one side the later dial supersedes the
  one it replaces (main's rule), which a join over an open session needs: a pure
  least-id rule made `connection_check`'s second-community join fail 3 runs in 8
  (the join's fresh session lost to the older one whenever its random id was
  larger), and restoring per-side supersession made it pass 10 in 10.
- **Bounded local history.** The engine's node gained one hook, `stale`: local ops
  newer ones supersede, purged with the shipped couriers (`Node.flush`). A purge
  deletes no shared op. The family names every scan position but the newest and,
  for this node and each node the newest scan visited, every retry clock and
  DNS-SD observation but the newest. Local discovery times come from a clock that
  never runs below the newest stored (`floor`).

Prior art: POC-6's address ops, POC-10's persisted invite bootstrap, POC-7's
bootstrap race (an advertisement never replaces an established session).

## What is proved

All laws are over code the app runs, rest on Lean's standard axioms only, and
have their premises checked on concrete inputs (`test:endpoints`).

| Claim | Laws |
|---|---|
| One attempt from each side: both ends select the same single session (the least id), whatever the arrival order or clocks; reconsidering the loser does not flap it; a side's redial supersedes | `Winner.choose_comm`, `Winner.choose_stable`, `Winner.exactly_one`, `kept_pair`, `redial_supersedes`, `both_choose_same`, `single_survivor`, `no_flapping` |
| Publications are the owner's, at most eight hints, expiring within a day; at most 24 candidates; backoff at most 60 s; every candidate tried within a cycle | `publication_auth`, `candidate_cap`, `candidate_visited`, `retry_eventually_due`, `Hints.bounded_cap`, `Hints.delay_bounded`, `Hints.fresh_expires` |
| The dialer's scan step is the cursor's | `page_run` (bridge: `Cursor.page`, `Cursor.next`) |
| A row filed throughout a window is visited within \|U\| + 2 steps, U every position filed meanwhile, wherever rows are inserted | `Cursor.visits`, `Cursor.dist_step`, `rows_strict`, `scan_visits` |
| `stale` never names the newest of a list, names every older one it reads, and the step's purge deletes them | `stale_sound`, `stale_complete`, `stale_gone`, `flush_notifies`, `stale_reads` |
| Reissue at least 60 s apart; unchanged hints at least half a day apart | `publish_gap`, `publish_refresh` |
| The planner's steps: a due clock plans an attempt and a retry op; an early one plans nothing | `plan_ready`, `plan_backoff`, `plan_after_backoff` |
| A reachable address in the candidates is attempted within \|L\|·(60000/δ + 2) visits δ apart, and again after any visit | `attempts_reach`, `attempt_within`, `reaches` |
| A visit whose plan is ready writes the retry clock and a courier of this node's request to the planned address | `member_attempts`, `attempt_sends` |
| Every node event with discovery enabled preserves shared ops and settles validation | `dial_reads`, `readOnly`, `setup_readOnly`, `step_moves`, `step_retains`, `step_settled` |

Together: a member admitted before a window of |U| + 2 dial ticks is visited in
it, and while it stays authorized and unconnected, a reachable address among its
candidates receives a request at least once every |L|·(60000/δ + 2) visits. Only
admins admit, so a hostile non-admin member cannot slow anyone's scan; its own
publications can name at most eight addresses for itself, and its sightings are
republished only by their target, under the same cap.

### Mutation controls

`tests/endpoints/mutations.py` changes the production source in its own copy of
the tree and requires the build to fail inside the intended law (an error within
that declaration's lines), four copies at a time. Fifteen controls:

| Mutant | Law it must break |
|---|---|
| arrival order picks the winner | `Winner.choose_comm` |
| no address cap | `Hints.bounded_cap` |
| inclusive expiry | `Hints.fresh_expires` |
| unbounded backoff | `Hints.delay_bounded` |
| retry every tick | the backoff example beside `retry_eventually_due` |
| unsigned publication | `publication_auth` |
| ready plan dropped | `plan_ready` |
| a direct store write from the planner | `plan_reads` (storage) |
| scan never wraps | `Cursor.dist_step` |
| `stale` names the newest | `olderOf_eval` (under `stale_sound`) |
| publication without the gap | `publish_gap` |
| attempt number repeats | `nextAttempt_eq` (under `reaches`) |
| an attempt without its courier | `attempt_sends` |
| `flush` keeps superseded ops | `flush_notifies` |
| the old route hook (real TCP) | the late-loser test's native socket count |

## What is assumed

- The store carries the dialer's state between ticks: each tick reads back the
  cursor and retry clock the previous one wrote (its local ops commit; the newest
  is the last written, which `floor` keeps true across restarts).
- The dial ticks, and a member's visits are at least δ > 0 apart in time.
- The member's row stays filed; its candidates and authorization are stable
  during the window.
- A request that reaches a reachable address under fair loss is eventually
  answered, and the answer delivered (the handshake's own progress); a request
  op can be built (the suite's Diffie-Hellman succeeds).
- Correct crypto and storage, available socket quotas, completing or cancellable
  native operations; clocks close enough that a live publication is not treated
  as future or expired.

## What is not yet proved

- The store carry above, through the full node step and the native runner
  (witnessed natively, not proved).
- The handshake's completion once a request is delivered (main's open bootstrap
  convergence item).
- A bound on a hostile member's shared endpoint ops. Like any shared op, the
  engine never deletes them (`purge_shared`); every discovery read stays capped
  whatever the history. An honest member's shared history grows by its address
  changes and two publications a day.
- Agreement when one side's two dials race: the ends may keep different ones,
  retire both, and dial again (no deadlock, but churn).
- Cost: a purge bounds its walk by counting the ops table (`count(*)`), so a
  tick that purges superseded local ops reads O(N) rows, as courier purges
  already do; that engine tradeoff is not changed here.
- Whole-app CPU and storage bounds; socket closure's native completion boundary.

## Real-network tests

Each named task builds what it runs in a 48 GiB systemd scope with swap off and
keeps its logs and databases under `out/endpoints`.

| Task | Result on this branch |
|---|---|
| `test:endpoints` | see the final run below |
| `test:endpoints-simultaneous` | pass: both processes answer one attempt each and keep the smaller id |
| `test:endpoints-late` | pass: a late, never-selected loser's socket is released; the old route hook fails |
| `test:endpoints-ops` | pass: a session from a signed endpoint publication |
| `test:endpoints-invite` | pass: a dead first invite address is skipped |
| `test:endpoints-lan` | pass: LAN DNS-SD, signed markers and publications both ways, each end's own publication lists its listening port |
| `test:endpoints-phone` | see the final run below |
| `test:endpoints-tailnet` | not run: see below |

### Why the Tailscale test cannot run on the desktop alone

On one machine, packets to the machine's own tailnet address never enter
Tailscale: `ip route get 100.67.2.56` on `desktop` gives `local 100.67.2.56 dev lo
table local`, while another node, `ip route get 100.110.168.19`, goes via
`dev tailscale0 table 52`. A same-host run would test loopback. The test needs a
second tailnet node. `clean-quiet-test` is that node: a separate Linux machine
behind the same eero Wi-Fi as the user's phone (they share the eero's NAT address
10.0.0.89). On 2026-11-01 it answered `tailscale ping` (7 ms, direct) but refused
SSH on port 22, including `tailscale ssh`, so the test could not start its
remote process. Either enable sshd there, or run a second, ephemeral tailscaled
on the desktop in its own network namespace (traffic then crosses both WireGuard
data planes); the latter adds a device to the tailnet and needs the owner's
login approval.
