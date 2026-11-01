# Peer endpoints: implementation and verification

Work is isolated on `peer-endpoints`, based on `origin/main` f325982. This is an
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
community ops and performs a tick that actually stores discovery actions.
SQLite/native refinement and the history-dependent validation budget have the
same boundaries as the existing storage work.

The axiom audit includes these laws. Mutation controls change the production
sources, require rejection in the intended law file, and retain failure logs:
arrival-order arbitration, missing address cap, inclusive expiry, unbounded
backoff, bypassed retry delay, unsigned publication, suppressed ready plan, and
a direct store write from a hook. Native witnesses use evaluated hypotheses;
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
| `test:endpoints` | Native validation, proof-premise witnesses, axiom audit, and source mutation controls. |
| `test:endpoints-invite` | Pass: a dead first invite address is skipped; the reachable second address bootstraps membership and encrypted signed-marker exchange. |
| `test:endpoints-ops` | Pass: two OS processes establish a session from a signed endpoint publication. |
| `test:endpoints-simultaneous` | Pass: each process independently answers one attempt; both keep the smaller of the two connection IDs, exchange markers, and retain one stable session. |
| `test:endpoints-lan` | Pass: two OS processes discover each other by LAN mDNS, exchange signed markers and endpoint publications, and report the correct listening ports. |
| `test:endpoints-phone` | Pass: desktop and Pixel 7 discover over LAN mDNS, exchange signed markers/publications, and report listening ports. Both retain the same session ID and shut down cleanly. |
| `test:endpoints-tailnet` | Not established: `clean-quiet-test` was offline and SSH preflight failed. No remote process or service was changed. |

The stronger simultaneous run is retained in
`out/endpoints/simultaneous-1793500739747644699`; its two answer IDs start
`cb7d8b5f` and `c62c6009`, and both peers retain `c62c6009`. The stronger LAN run
is in `out/endpoints/lan-1793501004216046946`, retaining `57e70da7` at both ends.
The stronger Pixel 7 run is in `out/endpoints/phone-1793501098`, retaining
`e4282070` at both ends. Initial failed phone runs are also retained: the locked
activity released its multicast lock and Android rejected sends. A separate
initial desktop shutdown failure exposed an async UDP receive cancellation
problem; the worker now polls and cancels the native receive promise.

Existing `test:join-fair` and the fairness certificate suite pass, including the
expected failing mutations. The full project check and generated proof-link
audit are run again after integration. Main is not promoted while the remote
network test and the remaining universal proof obligations are open.
