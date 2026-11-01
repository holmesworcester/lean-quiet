# Peer endpoints: implementation and verification

Work is isolated on `peer-endpoints`, merged with `origin/main` b44a7af. This is an
implementation and component-proof report, not a certificate that all requested
end-to-end progress obligations are complete. No iroh is used.

## Policy and prior art

POC-6's small signed address publications fit the existing shared-op engine.
POC-10 supplies the invite bootstrap-address pattern. POC-7's bootstrap race
motivates retaining authenticated sessions when new endpoint information arrives.
Its current iroh transport was not adopted. Keeping the minimum shared connection
op ID is simpler here than introducing direction ranks or a new handshake field:
both parties already possess that exact ID after the existing two-message Noise
exchange. Reversing local arrival order or clock values does not change it.

The app bundles up to eight LAN/tailnet IPv4 addresses in invites, excluding
Docker/bridge interfaces. Shared, signed `addresses` ops bind the publisher to
its admission's node key and carry up to eight detected plus observed endpoints
in total. The latest publication supersedes older ones, even after expiry.
Lifetime is at most five minutes. A peer signs a `sighting` of the authenticated
remote IP and listening port; the owner republishes it. An accepted socket's
transient source port is never advertised as its listening port.

All three sources use one address planner: invite, shared publication, and local
DNS-SD observation. It retains at most eight from each source (24 in total),
tries one address at a time, and persists a per-peer retry clock independent of
advertisement replacement. Backoff grows to 60 seconds. Each tick visits at most
two invite rows and two membership rows. The cursor and retry decisions are ops.
No initial empty publication is written before interface detection completes.

DNS-SD uses the existing vendored Lean mDNS codec and service code. LAN traffic
uses explicit LAN multicast interfaces, with a unique key-derived instance name.
Known tailnet seeds receive QU queries directly at UDP port 5353 and answer by
unicast, as specified by [RFC 6762 §5.5](https://www.rfc-editor.org/rfc/rfc6762.html#section-5.5).
This does not require Tailscale to carry multicast, and does not scan the tailnet.
Seeds come from known invite/endpoint addresses or explicit test arguments.

The Android activity holds a Wi-Fi multicast lock while resumed. The Pixel 7
test uses its own package, `com.holmes.leanquiet.endpoints`, dismisses the test
phone's keyguard, and keeps the screen awake. It does not clear the normal app.
The Pixel 10 Pro and the reserved MacBook were not used.

## Proof boundary

`DiscoveryLaws` proves agreement and exactly one selected ID for two distinct
simultaneous connections, invariance under direction/arrival-clock changes, and
stability when reconsidering the loser. It also proves publication authorization
and the address, expiry and retry-policy bounds. Actual socket retirement still
requires the existing native completion contract.

`DiscoveryProgress` proves that the actual planner returns the selected address
and retry op when its store reads supply eligible hints, that it refuses a plan
before the retry deadline, and that the maximum backoff suffices for its next
selected address. These laws use the existing advancing-entropy Held interpreter.
Concrete native witnesses check every premise for invite, signed publication and
DNS-SD observations. They are step results, not a universal liveness theorem.

`DiscoveryStorage` discharges the new hooks' read-only obligations and composes
Astra's existing `NodeTape.step_goes` theorem. With discovery enabled, every
actual node input preserves shared ops, and validation settles from a reachable,
settled store. Entropy may advance. A native witness starts with real signed
community ops and performs a tick that actually stores discovery actions. After
merging Astra’s catalog work, the theorem also keeps its catalog and durable
retry-store adapters enabled in that interpreter.
SQLite/native refinement and the history-dependent validation budget have the
same boundaries as the existing storage work.

The axiom audit includes these laws. Mutation controls change the production
sources, require rejection in the intended law file, and retain failure logs:
arrival-order arbitration, missing address cap, inclusive expiry, unbounded
backoff, bypassed retry delay, unsigned publication, suppressed ready plan, and
a direct store write from a hook. A ninth control runs real TCP with the old
selected-only route hook; it must fail because the late losing socket remains
allocated. Native witnesses use evaluated hypotheses;
the tests do not introduce `sorryAx` or native-decision axioms into the laws.

Still open are universal discovery-to-established-session progress under
fair-loss transport, fair cursor service under continuously adversarial admission
history, and a bound on accumulated immutable endpoint-op history. The active
address and per-tick caps do not prove a whole-app CPU or storage bound. These
are substantive remaining obligations. Progress also needs authorized peers,
correct crypto/storage, continued execution, available transport capacity,
completion or cancellation of native operations, and repeatedly usable addresses.
Shared expiry requires sufficiently compatible clocks.

## Reproduction and observed results

All endpoint tasks include their builds under a 48 GiB systemd user scope with
swap disabled and `TMPDIR=/mnt/storage/holmes-tmp`. Their scripts retain logs and
SQLite databases under `out/endpoints`. A network failure is a failure, not a
silently accepted skip.

| Mise task | Observed result |
|---|---|
| `test:endpoints` | Pass: 33 native checks, explicit theorem applications, axiom audit, eight proof mutations and the native socket-retirement mutation. |
| `test:endpoints-invite` | Pass: a dead first invite address is skipped; the reachable second address bootstraps membership and encrypted signed-marker exchange. |
| `test:endpoints-ops` | Pass: two OS processes establish a session from a signed endpoint publication. |
| `test:endpoints-simultaneous` | Pass: each process independently answers one attempt; both keep the smaller of the two connection IDs, exchange markers, and retain one stable session. |
| `test:endpoints-late` | Pass: test entropy forces the late reply above the existing winner; both processes retain one actual native socket reservation. Restoring the old route hook is a failing runtime control. |
| `test:endpoints-lan` | Pass: two OS processes discover each other by LAN mDNS, exchange signed markers and endpoint publications, and report the correct listening ports. |
| `test:endpoints-phone` | Pass: desktop and Pixel 7 discover over LAN mDNS, exchange signed markers/publications, and report listening ports. Both retain the same session ID and shut down cleanly. |
| `test:endpoints-tailnet` | Not established: `clean-quiet-test` was offline and SSH preflight failed. No remote process or service was changed. |

After merging b44a7af, the simultaneous run is retained in
`out/endpoints/simultaneous-1793503428049548379`: the two response IDs begin
`acd01d7e` and `614f3ff1`, and both peers keep `614f3ff1` with one native socket.
The deterministic late-loser run is
`out/endpoints/simultaneous-1793503437930410076` (both keep `13e036cb`).
The LAN run is `out/endpoints/lan-1793503448570286815` (both keep `631d46b7`),
and Pixel 7 is `out/endpoints/phone-1793503457` (both keep `55be1bc7`).

Failure artifacts are retained too. A delayed higher-ID attempt exposed an
unselected-route retirement bug. The hook now gives the node every authenticated
route before its common finish path retires losers. Restoring the old hook
still fails with two native sockets in
`out/endpoints/mutations/unrouted_loser-es4r7vqm`.
The merged database schema also exposed an observer race in
`out/endpoints/simultaneous-1793503285125150084`: observers were rerunning
schema/catalog migrations while the writer retired a session. Discovery and
test observers now use query-only connections to the initialized database.
Initial phone failures showed the locked activity releasing its multicast
lock; the test wakes the phone and dismisses its keyguard. An initial desktop
shutdown failure exposed UDP receive cancellation; the worker now polls and
cancels its native receive promise.

The complete axiom/build gate and native retirement control are in
`out/endpoints/final-proof-native-control.log`. The complete vacuity gate and
proof-link negative controls pass in `out/endpoints/merged-audits2.log`:
618 evidence entries cover all 618 linked declarations, including explicit
applications of all 23 endpoint laws. A metadata entry alone does not count:
the audit checks each witness's dependency on its named theorem, its axioms,
and that its native executable actually calls it.

Existing `test:join-fair` and the fairness certificate suite pass, including the
expected failing mutations. The full project check and generated proof-link
audit are run again after integration. Main is not promoted while the remote
network test and the remaining universal proof obligations are open.
